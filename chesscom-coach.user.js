// ==UserScript==
// @name         Chess.com Coach
// @namespace    hfy.chess.review
// @version      8.2
// @description  Coach panel for chess.com analysis boards: evaluation, win bar, and a spoken-style explanation of why each of your moves was good or bad (optional read-aloud). The wording is written word by word by a small built-in neural network. Also supports four-player chess (Teams) analysis boards with the built-in Titan engine.
// @match        https://www.chess.com/analysis*
// @match        https://www.chess.com/variants/4-player-chess/analysis*
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_getResourceText
// @grant        GM_setClipboard
// @grant        unsafeWindow
// @resource     STOCKFISH https://cdnjs.cloudflare.com/ajax/libs/stockfish.js/10.0.2/stockfish.js
// @connect      lichess.org
// @connect      chess-api.com
// @connect      cdnjs.cloudflare.com
// @connect      raw.githubusercontent.com
// @run-at       document-idle
// ==/UserScript==

(function coachMain() {
  'use strict';

  // 只在分析棋盘上运行：和开头的 @match 保持一致。
  // chess.com 很多是“页面内跳转”（地址变了但页面不重新加载），Tampermonkey 不会再检查 @match，
  // 所以地址一离开这里列的页面（比如点了“新对局”），面板就隐藏、朗读停下。
  const PAGES = [/^\/analysis/, /^\/variants\/4-player-chess\/analysis/];
  const onPage = () => PAGES.some((re) => re.test(location.pathname));

  const LICHESS_URL = 'https://lichess.org/api/cloud-eval?fen=';
  const CHESS_API_URL = 'https://chess-api.com/v1';
  const SF_URL = 'https://cdnjs.cloudflare.com/ajax/libs/stockfish.js/10.0.2/stockfish.js';
  const DOWN_MS = 60000; // 在线接口失败后，这段时间内直接用本地引擎
  const ONLINE_MS = 2000; // 每个局面在线引擎一共只等这么久（两个接口合起来算），超时马上改用本地引擎
  const START = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR';
  const FILES = 'abcdefgh';
  const VAL = { p: 1, n: 3, b: 3, r: 5, q: 9, k: 0 };
  const ORDER = ['losing', 'worse', 'equal', 'better', 'winning'];
  const BAD = ['inaccuracy', 'mistake', 'blunder', 'missedMate'];
  const COLORS = {
    mate: '#81b64c', mating: '#81b64c', best: '#81b64c', excellent: '#95b776', good: '#a3c97a',
    inaccuracy: '#f7c631', mistake: '#ffa459', blunder: '#fa412d', missedMate: '#fa412d',
  };
  const KN = [[1, 2], [2, 1], [-1, 2], [-2, 1], [1, -2], [2, -1], [-1, -2], [-2, -1]];
  const ROOK = [[1, 0], [-1, 0], [0, 1], [0, -1]];
  const BISHOP = [[1, 1], [1, -1], [-1, 1], [-1, -1]];
  const KG = ROOK.concat(BISHOP);

  // 稳定的“随机”：同一步棋每次生成的讲解一样，不会来回跳
  function hash(s) {
    let h = 2166136261;
    for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
    return h >>> 0;
  }

  // ---------- 棋盘工具 ----------
  function parseBoard(fen) {
    const b = {};
    fen.split(' ')[0].split('/').forEach((r, i) => {
      let f = 0;
      for (const ch of r) {
        if (/\d/.test(ch)) f += +ch;
        else { b[FILES[f] + (8 - i)] = ch; f++; }
      }
    });
    return b;
  }

  const colorOf = (p) => (p === p.toUpperCase() ? 'w' : 'b');
  const other = (c) => (c === 'w' ? 'b' : 'w');
  const sqXY = (s) => [FILES.indexOf(s[0]), +s[1] - 1];
  const xySq = (x, y) => FILES[x] + (y + 1);
  const onBoard = (x, y) => x >= 0 && x < 8 && y >= 0 && y < 8;

  function applyUci(b, uci) {
    const n = { ...b };
    const f = uci.slice(0, 2), t = uci.slice(2, 4), p = n[f];
    if (!p) return n;
    const [fx, fy] = sqXY(f), [tx] = sqXY(t);
    const low = p.toLowerCase();
    if (low === 'p' && fx !== tx && !n[t]) delete n[xySq(tx, fy)]; // 吃过路兵
    if (low === 'k' && Math.abs(tx - fx) === 2) { // 易位时车也要动
      const rf = tx > fx ? xySq(7, fy) : xySq(0, fy);
      n[xySq((fx + tx) / 2, fy)] = n[rf];
      delete n[rf];
    }
    delete n[f];
    n[t] = uci[4] ? (colorOf(p) === 'w' ? uci[4].toUpperCase() : uci[4]) : p;
    return n;
  }

  // sq 上的子攻击（或保护）的所有格子
  function pieceAttacks(b, sq) {
    const p = b[sq];
    if (!p) return [];
    const c = colorOf(p), t = p.toLowerCase(), [x, y] = sqXY(sq), out = [];
    const add = (X, Y) => { if (onBoard(X, Y)) out.push(xySq(X, Y)); };
    if (t === 'p') { const d = c === 'w' ? 1 : -1; add(x - 1, y + d); add(x + 1, y + d); }
    else if (t === 'n') KN.forEach(([dx, dy]) => add(x + dx, y + dy));
    else if (t === 'k') KG.forEach(([dx, dy]) => add(x + dx, y + dy));
    else {
      const dirs = t === 'r' ? ROOK : t === 'b' ? BISHOP : KG;
      for (const [dx, dy] of dirs) {
        for (let i = 1; i < 8; i++) {
          const X = x + dx * i, Y = y + dy * i;
          if (!onBoard(X, Y)) break;
          const s = xySq(X, Y);
          out.push(s);
          if (b[s]) break;
        }
      }
    }
    return out;
  }

  const attackersOf = (b, sq, by) => Object.keys(b).filter((s) => s !== sq && colorOf(b[s]) === by && pieceAttacks(b, s).includes(sq));
  const attacked = (b, sq, by) => attackersOf(b, sq, by).length > 0;

  // 这个子是否“悬着”：没保护却被攻击，或者被更便宜的子攻击
  function isHanging(b, sq) {
    const p = b[sq];
    if (!p) return false;
    const c = colorOf(p), atk = attackersOf(b, sq, other(c));
    if (!atk.length) return false;
    if (!attackersOf(b, sq, c).length) return true;
    return Math.min(...atk.map((s) => VAL[b[s].toLowerCase()] || 100)) < VAL[p.toLowerCase()];
  }

  function isPassed(b, sq, c) {
    const [x, y] = sqXY(sq), dir = c === 'w' ? 1 : -1, enemy = c === 'w' ? 'p' : 'P';
    for (let X = x - 1; X <= x + 1; X++) {
      for (let Y = y + dir; Y >= 0 && Y < 8; Y += dir) {
        if (onBoard(X, Y) && b[xySq(X, Y)] === enemy) return false;
      }
    }
    return true;
  }

  function matBal(b, me) {
    let s = 0;
    for (const p of Object.values(b)) s += (colorOf(p) === me ? 1 : -1) * VAL[p.toLowerCase()];
    return s;
  }

  function inCheck(fen) {
    const b = parseBoard(fen), turn = fen.split(' ')[1];
    const k = Object.keys(b).find((s) => b[s] === (turn === 'w' ? 'K' : 'k'));
    return k ? attacked(b, k, other(turn)) : false;
  }

  // 空着法：假设轮到的一方“什么都不走”，换对方走——用来问引擎“对方想干什么”
  function nullFen(fen) {
    if (!fen || inCheck(fen)) return null;
    const p = fen.split(' ');
    p[1] = p[1] === 'w' ? 'b' : 'w';
    p[3] = '-';
    return p.join(' ');
  }

  function moveInfo(b, uci) {
    if (!uci || uci.length < 4) return null;
    const f = uci.slice(0, 2), t = uci.slice(2, 4), p = b[f];
    if (!p) return null;
    const c = colorOf(p), low = p.toLowerCase();
    const [fx] = sqXY(f), [tx] = sqXY(t);
    let cap = b[t] ? b[t].toLowerCase() : null;
    if (low === 'p' && fx !== tx && !b[t]) cap = 'p';
    const after = applyUci(b, uci);
    const oppKing = Object.keys(after).find((s) => after[s] === (c === 'w' ? 'k' : 'K'));
    return {
      uci, from: f, to: t, piece: low, color: c, cap, promo: uci[4] || null,
      castle: low === 'k' && Math.abs(tx - fx) === 2 ? (tx > fx ? 'O-O' : 'O-O-O') : null,
      check: oppKing ? attacked(after, oppKing, c) : false,
      after,
    };
  }

  // 沿着引擎的变化走几步
  function playLine(b, pv, n) {
    const moves = [], boards = [b];
    let cb = b;
    for (let i = 0; i < n && pv && i < pv.length; i++) {
      const m = moveInfo(cb, pv[i]);
      if (!m) break;
      moves.push(m);
      cb = m.after;
      boards.push(cb);
    }
    return { moves, boards };
  }

  // 走完偶数步（双方都应对过）之后，我方子力的变化
  function lineMat(line, me, plies) {
    let k = Math.min(plies, line.moves.length);
    k -= k % 2;
    return matBal(line.boards[k], me) - matBal(line.boards[0], me);
  }

  function phaseOf(b, fen, exact) {
    let np = 0;
    for (const p of Object.values(b)) {
      const l = p.toLowerCase();
      if (l !== 'p' && l !== 'k') np += VAL[l];
    }
    if (np <= 26) return 'endgame';
    if (np >= 54 && (!exact || plyOf(fen) <= 24)) return 'opening';
    return 'middlegame';
  }

  // 对比两个局面，还原刚走的那步（UCI 格式）
  function diffMove(fenA, fenB) {
    const a = parseBoard(fenA), b = parseBoard(fenB);
    const from = [], to = [];
    for (const s of new Set([...Object.keys(a), ...Object.keys(b)])) {
      if (a[s] === b[s]) continue;
      if (a[s] && !b[s]) from.push(s);
      else if (b[s]) to.push(s);
    }
    if (!to.length || to.length > 2) return null;
    const mover = colorOf(b[to[0]]);
    if (to.some((s) => colorOf(b[s]) !== mover)) return null;
    const mf = from.filter((s) => colorOf(a[s]) === mover);
    if (!mf.length || mf.length !== to.length) return null;
    let f = mf[0], t = to[0];
    if (mf.length === 2) { // 王车易位
      f = mf.find((s) => a[s].toLowerCase() === 'k');
      t = to.find((s) => b[s].toLowerCase() === 'k');
      if (!f || !t) return null;
    }
    let uci = f + t;
    if (a[f].toLowerCase() === 'p' && b[t].toLowerCase() !== 'p') uci += b[t].toLowerCase();
    return { uci, mover };
  }

  const plyOf = (fen) => {
    const p = fen.split(' ');
    return (+p[5] - 1) * 2 + (p[1] === 'b' ? 1 : 0);
  };

  // ---------- 知识库和查询工具 ----------
  // 知识库：开局名称（按局面查，所以走法顺序不同也认得出；由 tools/build-kb.js 从 kb/openings.txt 生成后写在这里）、
  // 基本残局的结论、有讲解的术语。讲解要用到这些知识时不直接读表，而是通过下面的“查询工具”去查。
  const KB = {
    openings: /*KB_OPENINGS*/{"r1bqkbnr/pppp1ppp/2n5/4p3/2B1P3/5N2/PPPP1PPP/RNBQK2R b":"Italian Game","r1bqk1nr/pppp1ppp/2n5/2b1p3/2B1P3/5N2/PPPP1PPP/RNBQK2R w":"Giuoco Piano","r1bqk1nr/pppp1ppp/2n5/2b1p3/1PB1P3/5N2/P1PP1PPP/RNBQK2R b":"Evans Gambit","r1bqkb1r/pppp1ppp/2n2n2/4p3/2B1P3/5N2/PPPP1PPP/RNBQK2R w":"Two Knights Defense","r1bqkb1r/ppp2Npp/2n5/3np3/2B5/8/PPPP1PPP/RNBQK2R b":"Fried Liver Attack","r1bqkbnr/pppp1ppp/2n5/1B2p3/4P3/5N2/PPPP1PPP/RNBQK2R b":"Ruy Lopez","r1bqkbnr/1ppp1ppp/p1n5/1B2p3/4P3/5N2/PPPP1PPP/RNBQK2R w":"Ruy Lopez, Morphy Defense","r1bqkb1r/pppp1ppp/2n2n2/1B2p3/4P3/5N2/PPPP1PPP/RNBQK2R w":"Ruy Lopez, Berlin Defense","r1bqkbnr/1ppp1ppp/p1B5/4p3/4P3/5N2/PPPP1PPP/RNBQK2R b":"Ruy Lopez, Exchange Variation","r1bqk2r/1pppbppp/p1n2n2/4p3/B3P3/5N2/PPPP1PPP/RNBQ1RK1 w":"Closed Ruy Lopez","r1bqkb1r/1ppp1ppp/p1n5/4p3/B3n3/5N2/PPPP1PPP/RNBQ1RK1 w":"Open Ruy Lopez","r1bqkbnr/pppp1ppp/2n5/4p3/3PP3/5N2/PPP2PPP/RNBQKB1R b":"Scotch Game","r1bqkbnr/pppp1ppp/2n5/8/2BpP3/5N2/PPP2PPP/RNBQK2R b":"Scotch Gambit","r1bqkbnr/pppp1ppp/2n5/4p3/4P3/2N2N2/PPPP1PPP/R1BQKB1R b":"Three Knights Opening","r1bqkb1r/pppp1ppp/2n2n2/4p3/4P3/2N2N2/PPPP1PPP/R1BQKB1R w":"Four Knights Game","r1bqkbnr/pppp1ppp/2n5/4p3/4P3/2P2N2/PP1P1PPP/RNBQKB1R b":"Ponziani Opening","rnbqkb1r/pppp1ppp/5n2/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R w":"Petrov's Defense","rnbqkbnr/ppp2ppp/3p4/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R w":"Philidor Defense","rnbqkbnr/pppp1ppp/8/4p3/4PP2/8/PPPP2PP/RNBQKBNR b":"King's Gambit","rnbqkbnr/pppp1ppp/8/8/4Pp2/8/PPPP2PP/RNBQKBNR w":"King's Gambit Accepted","rnbqk1nr/pppp1ppp/8/2b1p3/4PP2/8/PPPP2PP/RNBQKBNR w":"King's Gambit Declined","rnbqkbnr/ppp2ppp/8/3pp3/4PP2/8/PPPP2PP/RNBQKBNR w":"Falkbeer Countergambit","rnbqkbnr/pppp1ppp/8/4p3/4P3/2N5/PPPP1PPP/R1BQKBNR b":"Vienna Game","rnbqkb1r/pppp1ppp/5n2/4p3/4PP2/2N5/PPPP2PP/R1BQKBNR b":"Vienna Gambit","rnbqkbnr/pppp1ppp/8/4p3/2B1P3/8/PPPP1PPP/RNBQK1NR b":"Bishop's Opening","rnbqkbnr/pppp1ppp/8/8/3QP3/8/PPP2PPP/RNB1KBNR b":"Center Game","rnbqkbnr/pppp1ppp/8/8/3pP3/2P5/PP3PPP/RNBQKBNR b":"Danish Gambit","rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w":"Sicilian Defense","rnbqkbnr/pp2pppp/3p4/2p5/3PP3/5N2/PPP2PPP/RNBQKB1R b":"Open Sicilian","r1bqkbnr/pp1ppppp/2n5/2p5/3PP3/5N2/PPP2PPP/RNBQKB1R b":"Open Sicilian","rnbqkbnr/pp1p1ppp/4p3/2p5/3PP3/5N2/PPP2PPP/RNBQKB1R b":"Open Sicilian","rnbqkb1r/1p2pppp/p2p1n2/8/3NP3/2N5/PPP2PPP/R1BQKB1R w":"Sicilian Defense, Najdorf Variation","rnbqkb1r/pp2pp1p/3p1np1/8/3NP3/2N5/PPP2PPP/R1BQKB1R w":"Sicilian Defense, Dragon Variation","r1bqkb1r/pp2pppp/2np1n2/8/3NP3/2N5/PPP2PPP/R1BQKB1R w":"Sicilian Defense, Classical Variation","rnbqkb1r/pp3ppp/3ppn2/8/3NP3/2N5/PPP2PPP/R1BQKB1R w":"Sicilian Defense, Scheveningen Variation","r1bqkb1r/pp1p1ppp/2n2n2/4p3/3NP3/2N5/PPP2PPP/R1BQKB1R w":"Sicilian Defense, Sveshnikov Variation","r1bqkbnr/pp1ppp1p/2n3p1/8/3NP3/8/PPP2PPP/RNBQKB1R w":"Sicilian Defense, Accelerated Dragon","r1bqkbnr/pp1p1ppp/2n1p3/8/3NP3/8/PPP2PPP/RNBQKB1R w":"Sicilian Defense, Taimanov Variation","rnbqkbnr/1p1p1ppp/p3p3/8/3NP3/8/PPP2PPP/RNBQKB1R w":"Sicilian Defense, Kan Variation","rnbqkbnr/pp1ppppp/8/2p5/4P3/2P5/PP1P1PPP/RNBQKBNR b":"Sicilian Defense, Alapin Variation","rnbqkbnr/pp1ppppp/8/2p5/4P3/2N5/PPPP1PPP/R1BQKBNR b":"Closed Sicilian","rnbqkbnr/pp1ppppp/8/8/3pP3/2P5/PP3PPP/RNBQKBNR b":"Smith-Morra Gambit","r1bqkbnr/pp1ppppp/2n5/1Bp5/4P3/5N2/PPPP1PPP/RNBQK2R b":"Sicilian Defense, Rossolimo Variation","rnbqkbnr/pp2pppp/3p4/1Bp5/4P3/5N2/PPPP1PPP/RNBQK2R b":"Sicilian Defense, Moscow Variation","r1bqkbnr/pp1ppppp/2n5/2p5/4PP2/2N5/PPPP2PP/R1BQKBNR b":"Grand Prix Attack","rnbqkbnr/pppp1ppp/4p3/8/4P3/8/PPPP1PPP/RNBQKBNR w":"French Defense","rnbqkbnr/ppp2ppp/4p3/3pP3/3P4/8/PPP2PPP/RNBQKBNR b":"French Defense, Advance Variation","rnbqkbnr/ppp2ppp/4p3/3P4/3P4/8/PPP2PPP/RNBQKBNR b":"French Defense, Exchange Variation","rnbqk1nr/ppp2ppp/4p3/3p4/1b1PP3/2N5/PPP2PPP/R1BQKBNR w":"French Defense, Winawer Variation","rnbqkb1r/ppp2ppp/4pn2/3p4/3PP3/2N5/PPP2PPP/R1BQKBNR w":"French Defense, Classical Variation","rnbqkbnr/ppp2ppp/4p3/3p4/3PP3/8/PPPN1PPP/R1BQKBNR b":"French Defense, Tarrasch Variation","rnbqkbnr/ppp2ppp/4p3/8/3Pp3/2N5/PPP2PPP/R1BQKBNR w":"French Defense, Rubinstein Variation","rnbqkbnr/pp1ppppp/2p5/8/4P3/8/PPPP1PPP/RNBQKBNR w":"Caro-Kann Defense","rnbqkbnr/pp2pppp/2p5/3pP3/3P4/8/PPP2PPP/RNBQKBNR b":"Caro-Kann Defense, Advance Variation","rnbqkbnr/pp2pppp/2p5/3P4/3P4/8/PPP2PPP/RNBQKBNR b":"Caro-Kann Defense, Exchange Variation","rnbqkbnr/pp2pppp/8/3p4/2PP4/8/PP3PPP/RNBQKBNR b":"Caro-Kann Defense, Panov Attack","rn1qkbnr/pp2pppp/2p5/5b2/3PN3/8/PPP2PPP/R1BQKBNR w":"Caro-Kann Defense, Classical Variation","rnbqkb1r/ppp1pp1p/3p1np1/8/3PP3/2N5/PPP2PPP/R1BQKBNR w":"Pirc Defense","rnbqkbnr/pppppp1p/6p1/8/4P3/8/PPPP1PPP/RNBQKBNR w":"Modern Defense","rnbqkb1r/pppppppp/5n2/8/4P3/8/PPPP1PPP/RNBQKBNR w":"Alekhine's Defense","rnbqkbnr/ppp1pppp/8/3p4/4P3/8/PPPP1PPP/RNBQKBNR w":"Scandinavian Defense","rnb1kbnr/ppp1pppp/8/q7/8/2N5/PPPP1PPP/R1BQKBNR w":"Scandinavian Defense, Main Line","r1bqkbnr/pppppppp/2n5/8/4P3/8/PPPP1PPP/RNBQKBNR w":"Nimzowitsch Defense","rnbqkbnr/p1pppppp/1p6/8/4P3/8/PPPP1PPP/RNBQKBNR w":"Owen's Defense","rnbqkbnr/ppp1pppp/8/3p4/2PP4/8/PP2PPPP/RNBQKBNR b":"Queen's Gambit","rnbqkbnr/ppp1pppp/8/8/2pP4/8/PP2PPPP/RNBQKBNR w":"Queen's Gambit Accepted","rnbqkbnr/ppp2ppp/4p3/3p4/2PP4/8/PP2PPPP/RNBQKBNR w":"Queen's Gambit Declined","rnbqkb1r/ppp2ppp/4pn2/3P4/3P4/2N5/PP2PPPP/R1BQKBNR b":"Queen's Gambit Declined, Exchange Variation","rnbqkbnr/pp2pppp/2p5/3p4/2PP4/8/PP2PPPP/RNBQKBNR w":"Slav Defense","rnbqkb1r/pp3ppp/2p1pn2/3p4/2PP4/2N2N2/PP2PPPP/R1BQKB1R w":"Semi-Slav Defense","rnbqkbnr/pp3ppp/4p3/2pp4/2PP4/2N5/PP2PPPP/R1BQKBNR w":"Tarrasch Defense","rnbqkbnr/ppp2ppp/8/3pp3/2PP4/8/PP2PPPP/RNBQKBNR w":"Albin Countergambit","r1bqkbnr/ppp1pppp/2n5/3p4/2PP4/8/PP2PPPP/RNBQKBNR w":"Chigorin Defense","rnbqkbnr/ppp1pppp/8/3p4/3P1B2/8/PPP1PPPP/RN1QKBNR b":"London System","rnbqkb1r/pppppppp/5n2/8/3P1B2/8/PPP1PPPP/RN1QKBNR b":"London System","rnbqkb1r/ppp1pppp/5n2/3p4/3P1B2/5N2/PPP1PPPP/RN1QKB1R b":"London System","rnbqkb1r/ppp1pppp/5n2/3p4/3P4/4PN2/PPP2PPP/RNBQKB1R b":"Colle System","rnbqkbnr/ppp1pppp/8/3p4/3PP3/8/PPP2PPP/RNBQKBNR b":"Blackmar-Diemer Gambit","rnbqk2r/ppppppbp/5np1/8/2PP4/2N5/PP2PPPP/R1BQKBNR w":"King's Indian Defense","rnbq1rk1/ppp1ppbp/3p1np1/8/2PPP3/2N2N2/PP2BPPP/R1BQK2R b":"King's Indian Defense, Classical Variation","rnbqk2r/ppp1ppbp/3p1np1/8/2PPP3/2N2P2/PP4PP/R1BQKBNR b":"King's Indian Defense, Samisch Variation","rnbqkb1r/ppp1pp1p/5np1/3p4/2PP4/2N5/PP2PPPP/R1BQKBNR w":"Grunfeld Defense","rnbqk2r/pppp1ppp/4pn2/8/1bPP4/2N5/PP2PPPP/R1BQKBNR w":"Nimzo-Indian Defense","rnbqkb1r/p1pp1ppp/1p2pn2/8/2PP4/5N2/PP2PPPP/RNBQKB1R w":"Queen's Indian Defense","rnbqk2r/pppp1ppp/4pn2/8/1bPP4/5N2/PP2PPPP/RNBQKB1R w":"Bogo-Indian Defense","rnbqkb1r/pppp1ppp/4pn2/8/2PP4/6P1/PP2PP1P/RNBQKBNR b":"Catalan Opening","rnbqkb1r/pp1ppppp/5n2/2p5/2PP4/8/PP2PPPP/RNBQKBNR w":"Benoni Defense","rnbqkb1r/pp1p1ppp/4pn2/2pP4/2P5/8/PP2PPPP/RNBQKBNR w":"Modern Benoni","rnbqkb1r/p2ppppp/5n2/1ppP4/2P5/8/PP2PPPP/RNBQKBNR w":"Benko Gambit","rnbqkb1r/pppp1ppp/5n2/4p3/2PP4/8/PP2PPPP/RNBQKBNR w":"Budapest Gambit","rnbqkb1r/ppp1pppp/3p1n2/8/2PP4/8/PP2PPPP/RNBQKBNR w":"Old Indian Defense","rnbqkb1r/pppppppp/5n2/6B1/3P4/8/PPP1PPPP/RN1QKBNR b":"Trompowsky Attack","rnbqkb1r/pppp1ppp/4pn2/6B1/3P4/5N2/PPP1PPPP/RN1QKB1R b":"Torre Attack","rnbqkbnr/ppppp1pp/8/5p2/3P4/8/PPP1PPPP/RNBQKBNR w":"Dutch Defense","rnbqkb1r/ppppp2p/5np1/5p2/3P4/6P1/PPP1PPBP/RNBQK1NR w":"Dutch Defense, Leningrad Variation","rnbqkbnr/pppp1ppp/8/4p3/3P4/8/PPP1PPPP/RNBQKBNR w":"Englund Gambit","rnbqkbnr/pppppppp/8/8/2P5/8/PP1PPPPP/RNBQKBNR b":"English Opening","rnbqkbnr/pp1ppppp/8/2p5/2P5/8/PP1PPPPP/RNBQKBNR w":"English Opening, Symmetrical Variation","rnbqkbnr/pppp1ppp/8/4p3/2P5/8/PP1PPPPP/RNBQKBNR w":"English Opening, Reversed Sicilian","rnbqkbnr/ppp1pppp/8/3p4/2P5/5N2/PP1PPPPP/RNBQKB1R b":"Reti Opening","rnbqkbnr/ppp1pppp/8/3p4/8/5NP1/PPPPPP1P/RNBQKB1R b":"King's Indian Attack","rnbqkbnr/pppppppp/8/8/5P2/8/PPPPP1PP/RNBQKBNR b":"Bird's Opening","rnbqkbnr/pppppppp/8/8/8/1P6/P1PPPPPP/RNBQKBNR b":"Larsen's Opening","rnbqkbnr/pppppppp/8/8/1P6/8/P1PPPPPP/RNBQKBNR b":"Polish Opening","rnbqkbnr/pppppppp/8/8/6P1/8/PPPPPP1P/RNBQKBNR b":"Grob Opening","rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b":"King's Pawn Opening","rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b":"Queen's Pawn Opening","rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w":"Open Game","rnbqkbnr/pppp1ppp/8/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R b":"King's Knight Opening","rnbqkbnr/ppp1pppp/8/3p4/3P4/8/PPP1PPPP/RNBQKBNR w":"Closed Game","rnbqkb1r/pppppppp/5n2/8/3P4/8/PPP1PPPP/RNBQKBNR w":"Indian Defense","rnbqkbnr/pppp1ppp/8/4p2Q/4P3/8/PPPP1PPP/RNB1KBNR b":"Wayward Queen Attack","rnbqkbnr/pppp1ppp/8/4p3/4P3/5Q2/PPPP1PPP/RNB1KBNR b":"Napoleon Opening","rnbqkbnr/pppp2pp/5p2/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R w":"Damiano Defense","rnbqkbnr/pppp2pp/8/4pp2/4P3/5N2/PPPP1PPP/RNBQKB1R w":"Latvian Gambit","rnbqkbnr/ppp2ppp/8/3pp3/4P3/5N2/PPPP1PPP/RNBQKB1R w":"Elephant Gambit","r1bqkb1r/pppp1ppp/2n2n2/4N3/4P3/8/PPPP1PPP/RNBQKB1R w":"Stafford Gambit","r1bqk1nr/ppppbppp/2n5/4p3/2B1P3/5N2/PPPP1PPP/RNBQK2R w":"Hungarian Defense","r1bqk1nr/pppp1ppp/2n5/2b1p3/2B1P3/3P1N2/PPP2PPP/RNBQK2R b":"Giuoco Pianissimo","r1bqkbnr/pppp1ppp/8/4p3/2BnP3/5N2/PPPP1PPP/RNBQK2R w":"Blackburne Shilling Gambit","r1bqkb1r/pppp1ppp/2n2n2/4p1N1/2B1P3/8/PPPP1PPP/RNBQK2R b":"Italian Game, Knight Attack","r1bqk2r/pppp1ppp/2n2n2/2b1p1N1/2B1P3/8/PPPP1PPP/RNBQK2R w":"Traxler Counterattack","r1bqk1nr/pppp1Bpp/2n5/2b1p3/4P3/5N2/PPPP1PPP/RNBQK2R b":"Jerome Gambit","r1bqkb1r/pppp1ppp/2n2n2/4N3/4P3/2N5/PPPP1PPP/R1BQKB1R b":"Halloween Gambit","rnbqkbnr/pp1ppppp/8/2p5/2B1P3/8/PPPP1PPP/RNBQK1NR b":"Sicilian Defense, Bowdler Attack","rnbqkbnr/pp1ppp1p/6p1/2p5/4P3/5N2/PPPP1PPP/RNBQKB1R w":"Sicilian Defense, Hyperaccelerated Dragon","rnbqkbnr/pppppppp/8/8/8/6P1/PPPPPP1P/RNBQKBNR b":"King's Fianchetto Opening"}/*END_KB*/,
    // 基本残局：一方只剩王时，另一方除了王还剩什么 → 名称和理论结论
    endgames: {
      Q: { name: 'king and queen against king', verdict: 'win' },
      R: { name: 'king and rook against king', verdict: 'win' },
      BB: { name: 'two bishops against a lone king', verdict: 'win' },
      BN: { name: 'bishop and knight against a lone king', verdict: 'win' },
      B: { name: 'king and bishop against king', verdict: 'draw' },
      N: { name: 'king and knight against king', verdict: 'draw' },
      NN: { name: 'two knights against a lone king', verdict: 'draw' },
    },
    // 术语表：识别出来的棋理 → 术语条目。讲解里第一次用到某个术语时补一句解释（解释的句子由语言模型来写：define.条目）
    glossary: {
      fork: 'fork', pin: 'pin', skewer: 'skewer', discovered: 'discovered', outpost: 'outpost', fianchetto: 'fianchetto', luft: 'luft',
      battery: 'battery', doubleRooks: 'battery', passed: 'passed', openFile: 'openFile', bishopPair: 'bishopPair', rook7th: 'rook7th',
      removeDefender: 'removeDefender', rookBehind: 'rookBehind', opposition: 'opposition',
    },
    // 开局原则：讲到开局里的毛病时，第一次补一句它背后的原则（principle.条目）
    principles: { knightRim: 'knightRim', sameTwice: 'sameTwice', blockPawn: 'blockPawn', earlyQueen: 'earlyQueen', kingWalk: 'kingWalk' },
    // 有名字的将杀
    mates: { backRank: 'back-rank mate', smothered: 'smothered mate', scholar: "Scholar's Mate", support: 'support mate' },
  };

  // 查询工具：仿照 MCP 的形式——每个工具有名字、说明、参数说明，一律通过 callTool(名字, 参数) 调用；
  // 查到了返回结果，查不到返回 null；每次调用都记进 log（鼠标停在面板的评级上，能看到这段讲解查到了什么）。
  // 棋盘标注也是工具（board_arrow / board_circle，都带颜色参数）：讲解时调用，面板照着调用记录在棋盘上画出来。
  const MARK_COLORS = { red: '#fa412d', green: '#81b64c', yellow: '#f7c631', orange: '#ffa459', blue: '#52b1dc' };
  const isSq = (x) => typeof x === 'string' && /^[a-h][1-8]$/.test(x);
  const TOOLS = {
    opening_lookup: {
      description: 'Name of the opening for a position, if it is a known one',
      params: { fen: 'position in FEN' },
      run: ({ fen }) => {
        const f = fen.split(' '), name = KB.openings[f[0] + ' ' + f[1]];
        return name ? { name } : null;
      },
    },
    endgame_lookup: {
      description: 'Basic endgame where one side has only the king, with its theoretical result',
      params: { fen: 'position in FEN' },
      run: ({ fen }) => {
        const b = parseBoard(fen), side = { w: [], b: [] };
        for (const p of Object.values(b)) if (p.toLowerCase() !== 'k') side[colorOf(p)].push(p.toUpperCase());
        if (side.w.length && side.b.length) return null;
        const strong = side.w.length ? 'w' : side.b.length ? 'b' : null, sig = strong ? side[strong].sort().join('') : '';
        const e = KB.endgames[sig];
        if (!e) return null;
        let verdict = e.verdict;
        if (sig === 'BB') { // 两个象要一个走白格、一个走黑格才杀得了王
          const shade = Object.keys(b).filter((s) => b[s].toUpperCase() === 'B').map((s) => (sqXY(s)[0] + sqXY(s)[1]) % 2);
          if (shade[0] === shade[1]) verdict = 'draw';
        }
        return { name: e.name, verdict, strong };
      },
    },
    glossary_lookup: {
      description: 'Glossary entry that explains a tactic or concept, if there is one',
      params: { term: 'name of the tactic or concept' },
      run: ({ term }) => (KB.glossary[term] ? { entry: KB.glossary[term] } : null),
    },
    principle_lookup: {
      description: 'Opening principle behind a warning about a move, if there is one',
      params: { topic: 'what the warning is about' },
      run: ({ topic }) => (KB.principles[topic] ? { entry: KB.principles[topic] } : null),
    },
    mate_pattern_lookup: {
      description: 'Name of the checkmate pattern on the board, if it is a known one',
      params: { position: 'the board after the mating move (square → piece)', move: 'the mating move, e.g. d1d8', opening: 'true if the game is still in the opening' },
      run: ({ position: b, move, opening }) => {
        const to = move.slice(2, 4), p = b[to];
        if (!p) return null;
        const c = colorOf(p), opp = other(c), t = p.toLowerCase();
        const ksq = Object.keys(b).find((sq) => b[sq] === (opp === 'w' ? 'K' : 'k'));
        if (!ksq) return null;
        const [kx, ky] = sqXY(ksq), [tx, ty] = sqXY(to), homeY = opp === 'w' ? 0 : 7;
        const adj = KG.map(([dx, dy]) => [kx + dx, ky + dy]).filter(([X, Y]) => onBoard(X, Y)).map(([X, Y]) => xySq(X, Y));
        const own = (sq) => !!b[sq] && colorOf(b[sq]) === opp; // 王身边的格子被它自己的子占着
        let entry = null;
        if (t === 'n' && adj.every(own)) entry = 'smothered';
        else if ((t === 'r' || t === 'q') && ky === homeY && ty === homeY && adj.filter((sq) => sqXY(sq)[1] !== homeY).every(own)) entry = 'backRank';
        else if (t === 'q' && opening && to === (opp === 'b' ? 'f7' : 'f2')) entry = 'scholar';
        else if (t === 'q' && Math.max(Math.abs(tx - kx), Math.abs(ty - ky)) === 1 && attacked(b, to, c)) entry = 'support';
        return entry ? { entry, name: KB.mates[entry] } : null;
      },
    },
    board_arrow: {
      description: 'Draw an arrow on the board from one square to another',
      params: { from: 'square the arrow starts on, e.g. g1', to: 'square it points to', color: 'red | green | yellow | orange | blue', note: 'what the arrow shows (optional)' },
      run: ({ from, to, color, note }) => (isSq(from) && isSq(to) && from !== to ? { draw: 'arrow', from, to, color: MARK_COLORS[color] ? color : 'yellow', note: note || '' } : null),
    },
    board_circle: {
      description: 'Circle one square on the board',
      params: { square: 'square to circle, e.g. e5', color: 'red | green | yellow | orange | blue', note: 'what the circle shows (optional)' },
      run: ({ square, color, note }) => (isSq(square) ? { draw: 'circle', square, color: MARK_COLORS[color] ? color : 'yellow', note: note || '' } : null),
    },
  };
  function callTool(name, args, log) {
    const t = TOOLS[name], result = t ? t.run(args) : null;
    if (log) log.push({ tool: name, args, result });
    return result;
  }

  // ---------- 这步棋在干什么：双击、威胁、白吃、兑换、救子、出子… ----------
  const TAG_ORDER = ['escapeCheck', 'fork', 'discovered', 'skewer', 'pin', 'recapture', 'freeCapture', 'sacCap', 'winTrade', 'threat', 'rescue', 'trade', 'develop', 'center', 'passed', 'openFile', 'semiOpen',
    'bishopPair', 'outpost', 'rook7th', 'doubleRooks', 'battery', 'tradeAhead', 'kingActive', 'fianchetto', 'connectRooks', 'luft',
    'removeDefender', 'rookBehind', 'opposition',
    'earlyQueen', 'kingShield', 'kingWalk', 'doublePawns', 'knightRim', 'sameTwice', 'blockPawn'];

  function analyzeMove(b, m, phase) {
    const tags = [];
    if (!m) return tags;
    const me = m.color, opp = other(me), a = m.after;
    const home = me === 'w' ? '1' : '8';

    // 走之前自己的王被将军：这步首先是在解将
    const myKing = Object.keys(b).find((s) => b[s] === (me === 'w' ? 'K' : 'k'));
    if (myKing && attacked(b, myKing, opp)) tags.push({ t: 'escapeCheck' });

    if (m.cap) {
      const deficit = -matBal(b, me); // 走之前少了多少子力（通常是对方刚吃了我的子）
      if (deficit > 0 && VAL[m.cap] <= deficit + 1) tags.push({ t: 'recapture', cap: m.cap });
      else if (!attacked(b, m.to, opp)) tags.push({ t: 'freeCapture', cap: m.cap });
      else if (VAL[m.cap] > VAL[m.piece]) tags.push({ t: 'winTrade', piece: m.piece, cap: m.cap });
      else if (VAL[m.cap] === VAL[m.piece]) tags.push({ t: 'trade', piece: m.piece, cap: m.cap });
      else tags.push({ t: 'sacCap', piece: m.piece, cap: m.cap }); // 用大子吃有保护的小子
    }

    if (!m.castle && !isHanging(a, m.to)) {
      // 攻击目标：王、比自己值钱的子、没保护的子；兵只算“攻击比保护多”的
      const targets = pieceAttacks(a, m.to)
        .filter((s) => a[s] && colorOf(a[s]) === opp)
        .filter((s) => {
          const t = a[s].toLowerCase();
          if (t === 'p') return attackersOf(a, s, me).length > attackersOf(a, s, opp).length;
          return t === 'k' || VAL[t] > VAL[m.piece] || !attacked(a, s, opp);
        })
        .map((s) => ({ p: a[s].toLowerCase(), sq: s }));
      if (targets.length >= 2) tags.push({ t: 'fork', piece: m.piece, targets });
      else if (targets.length === 1 && targets[0].p !== 'k') tags.push({ t: 'threat', piece: m.piece, target: targets[0] });

      // 牵制 / 串打：远程子沿线看到的前两个子都是对方的
      if ('brq'.includes(m.piece)) {
        const [x, y] = sqXY(m.to), dirs = m.piece === 'r' ? ROOK : m.piece === 'b' ? BISHOP : KG;
        const worth = (p) => (p === 'k' ? 100 : VAL[p]);
        for (const [dx, dy] of dirs) {
          const seen = [];
          for (let i = 1; i < 8 && seen.length < 2; i++) {
            const X = x + dx * i, Y = y + dy * i;
            if (!onBoard(X, Y)) break;
            const pc = a[xySq(X, Y)];
            if (!pc) continue;
            if (colorOf(pc) !== opp) break;
            seen.push({ p: pc.toLowerCase(), sq: xySq(X, Y) });
          }
          if (seen.length < 2) continue;
          const [front, behind] = seen;
          if (front.p !== 'p' && front.p !== 'k' && worth(behind.p) > worth(front.p) && (behind.p === 'k' || VAL[behind.p] >= 5)) {
            tags.push({ t: 'pin', piece: m.piece, pinned: front, behind });
          } else if (['k', 'q', 'r'].includes(front.p) && behind.p !== 'p' && worth(front.p) > worth(behind.p)
            && (!attacked(a, behind.sq, opp) || VAL[behind.p] > VAL[m.piece])) {
            tags.push({ t: 'skewer', piece: m.piece, front, behind });
          }
        }
      }
    }

    // 闪击：走开的子原本挡着自己的远程子，现在远程子打到了对方值钱或没保护的子
    if (!m.castle) {
      for (const s of Object.keys(a)) {
        const pc = a[s];
        if (s === m.to || colorOf(pc) !== me || !'brq'.includes(pc.toLowerCase())) continue;
        const before = new Set(pieceAttacks(b, s));
        const hit = pieceAttacks(a, s).find((t) => !before.has(t) && a[t] && colorOf(a[t]) === opp
          && (a[t].toLowerCase() === 'k' || VAL[a[t].toLowerCase()] > VAL[pc.toLowerCase()] || !attacked(a, t, opp)));
        if (hit) { tags.push({ t: 'discovered', piece: pc.toLowerCase(), target: { p: a[hit].toLowerCase(), sq: hit } }); break; }
      }
    }

    // 保护：原本悬着的己方子（不是走的这个），走完这步不再悬着
    for (const s of Object.keys(b)) {
      const pc = b[s];
      if (s === m.from || colorOf(pc) !== me || 'pk'.includes(pc.toLowerCase()) || a[s] !== pc) continue;
      if (isHanging(b, s) && !isHanging(a, s)) { tags.push({ t: 'defend', target: { p: pc.toLowerCase(), sq: s } }); break; }
    }

    if (!m.cap && m.piece !== 'p' && m.piece !== 'k' && isHanging(b, m.from) && !isHanging(a, m.to)) {
      tags.push({ t: 'rescue', piece: m.piece });
    }

    if (phase === 'opening') {
      if ((m.piece === 'n' || m.piece === 'b') && m.from[1] === home) tags.push({ t: 'develop', piece: m.piece });
      if (m.piece === 'q') tags.push({ t: 'earlyQueen' });
      if (m.piece === 'k' && !m.castle) tags.push({ t: 'kingWalk' });
    }
    if (['d4', 'e4', 'd5', 'e5'].includes(m.to) && (m.piece === 'p' || m.piece === 'n')) tags.push({ t: 'center' });

    if (m.piece === 'r' && m.from[0] !== m.to[0]) {
      const pawns = [1, 2, 3, 4, 5, 6, 7, 8].map((r) => a[m.to[0] + r]).filter((p) => p && p.toLowerCase() === 'p');
      if (!pawns.length) tags.push({ t: 'openFile' });
      else if (!pawns.some((p) => colorOf(p) === me)) tags.push({ t: 'semiOpen' });
    }

    if (m.piece === 'p' && !m.promo && isPassed(a, m.to, me)) {
      tags.push({ t: 'passed', rank: me === 'w' ? +m.to[1] : 9 - +m.to[1] });
    }

    if (m.piece === 'p' && phase !== 'endgame') {
      const k = Object.keys(b).find((s) => b[s] === (me === 'w' ? 'K' : 'k'));
      if (k && k[1] === home && (('gh'.includes(k[0]) && 'fgh'.includes(m.from[0])) || ('abc'.includes(k[0]) && 'abc'.includes(m.from[0])))) {
        tags.push({ t: 'kingShield' });
      }
    }

    // ---- 更专业的棋理 ----
    const myPawn = me === 'w' ? 'P' : 'p', oppPawn = me === 'w' ? 'p' : 'P', dir = me === 'w' ? 1 : -1;
    const [tx, ty] = sqXY(m.to), safe = !isHanging(a, m.to);
    const count = (bd, ch) => Object.values(bd).filter((p) => p === ch).length;

    // 前哨：马站到第五、六横线，有自己的兵保护，而且两边相邻的线上、它前方已经没有能来赶它的对方的兵
    if (m.piece === 'n' && safe) {
      const rel = me === 'w' ? ty : 7 - ty;
      const guarded = [tx - 1, tx + 1].some((X) => onBoard(X, ty - dir) && a[xySq(X, ty - dir)] === myPawn);
      let chased = false;
      for (const X of [tx - 1, tx + 1]) for (let Y = ty + dir; onBoard(X, Y); Y += dir) if (a[xySq(X, Y)] === oppPawn) chased = true;
      if ((rel === 4 || rel === 5) && guarded && !chased) tags.push({ t: 'outpost', piece: 'n' });
    }

    // 车到第七横线：那条线上还有对方的兵，而且对方的王被压在底线（两样都成立，“打兵”和“困王”才都说得通）
    if (m.piece === 'r' && safe && m.from[1] !== m.to[1] && m.to[1] === (me === 'w' ? '7' : '2')) {
      const oppKing = Object.keys(a).find((s) => a[s] === (me === 'w' ? 'k' : 'K'));
      if (FILES.split('').some((f) => a[f + m.to[1]] === oppPawn) && oppKing && oppKing[1] === (me === 'w' ? '8' : '1')) tags.push({ t: 'rook7th' });
    }

    // 叠车 / 后车同线：走到一条没有自己兵的线上，和另一个重子之间没有别的子
    if ((m.piece === 'r' || m.piece === 'q') && safe && m.from[0] !== m.to[0] && ![1, 2, 3, 4, 5, 6, 7, 8].some((r) => a[m.to[0] + r] === myPawn)) {
      let partner = null;
      for (const d of [1, -1]) {
        for (let Y = ty + d; onBoard(tx, Y); Y += d) {
          const pc = a[xySq(tx, Y)];
          if (!pc) continue;
          if (colorOf(pc) === me && 'rq'.includes(pc.toLowerCase())) partner = pc.toLowerCase();
          break;
        }
      }
      if (partner === 'r' && m.piece === 'r') tags.push({ t: 'doubleRooks' });
      else if (partner && partner !== m.piece) tags.push({ t: 'battery' });
    }

    // 双象：用马换掉对方的一个象，自己两个象都还在，对方只剩一个
    if (m.cap === 'b' && m.piece === 'n' && count(a, me === 'w' ? 'B' : 'b') === 2 && count(b, me === 'w' ? 'b' : 'B') === 2) tags.push({ t: 'bishopPair' });

    // 多子时兑子：已经多出至少一个轻子，再做等价交换
    if (tags.some((x) => x.t === 'trade') && matBal(b, me) >= 3) tags.push({ t: 'tradeAhead' });

    // 侧翼出象：象从底线走到马前兵让出来的那一格，站上大斜线
    if (m.piece === 'b' && m.from[1] === home && phase !== 'endgame') {
      const pawnSq = { g2: 'g3', b2: 'b3', g7: 'g6', b7: 'b6' }[m.to];
      if (pawnSq && m.to[1] === (me === 'w' ? '2' : '7') && a[pawnSq] === myPawn) tags.push({ t: 'fianchetto' });
    }

    // 连车：走完之后，底线上两个车之间没有别的子了
    if (phase !== 'endgame') {
      const connected = (bd) => {
        const rooks = Object.keys(bd).filter((s) => bd[s] === (me === 'w' ? 'R' : 'r'));
        if (rooks.length !== 2 || rooks[0][1] !== home || rooks[1][1] !== home) return false;
        const xs = rooks.map((s) => sqXY(s)[0]).sort((p, q) => p - q);
        for (let X = xs[0] + 1; X < xs[1]; X++) if (bd[FILES[X] + home]) return false;
        return true;
      };
      if (!connected(b) && connected(a)) tags.push({ t: 'connectRooks' });
    }

    const myKing2 = Object.keys(a).find((s) => a[s] === (me === 'w' ? 'K' : 'k'));
    // 给王留气口：王在底线、面前三格全是自己的兵，把其中一个兵挺一格，空出来的格子对方打不到
    if (m.piece === 'p' && !m.cap && phase !== 'opening' && myKing2 && myKing2[1] === home && Math.abs(+m.to[1] - +m.from[1]) === 1) {
      const [kx, ky] = sqXY(myKing2);
      const front = [kx - 1, kx, kx + 1].filter((X) => onBoard(X, ky + dir)).map((X) => xySq(X, ky + dir));
      if (front.includes(m.from) && front.every((s) => b[s] === myPawn) && !attacked(a, m.from, opp)) tags.push({ t: 'luft' });
    }

    // 消除保护：吃掉的那个子原来保护着对方另一个子，现在那个子没人保护、还被我攻击着
    if (m.cap) {
      const guarded = pieceAttacks(b, m.to);
      const hit = Object.keys(a).find((s) => s !== m.to && colorOf(a[s]) === opp && VAL[a[s].toLowerCase()] >= 3 && guarded.includes(s) && !isHanging(b, s) && isHanging(a, s));
      if (hit) tags.push({ t: 'removeDefender', target: { p: a[hit].toLowerCase(), sq: hit } });
    }

    // 残局里车走到通路兵的后面（自己的或对方的），中间没有别的子
    if (m.piece === 'r' && phase === 'endgame' && m.from[0] !== m.to[0]) {
      const [rx, ry] = sqXY(m.to);
      for (let Y = 0; Y < 8; Y++) {
        const s = xySq(rx, Y), p = a[s];
        if (!p || p.toLowerCase() !== 'p' || !isPassed(a, s, colorOf(p))) continue;
        if ((ry - Y) * (colorOf(p) === 'w' ? 1 : -1) >= 0) continue; // 车要在兵出发的那一边
        let clear = true;
        for (let y = Math.min(ry, Y) + 1; y < Math.max(ry, Y); y++) if (a[xySq(rx, y)]) clear = false;
        if (clear) { tags.push({ t: 'rookBehind' }); break; }
      }
    }

    // 对王：只剩王和兵，两个王正对着、中间隔一格，轮到对方走
    if (m.piece === 'k' && phase === 'endgame' && Object.values(a).every((p) => 'kp'.includes(p.toLowerCase())) && Object.values(a).some((p) => p.toLowerCase() === 'p')) {
      const ok = Object.keys(a).find((s) => a[s] === (me === 'w' ? 'k' : 'K'));
      if (ok) {
        const [x1, y1] = sqXY(m.to), [x2, y2] = sqXY(ok);
        if ((x1 === x2 && Math.abs(y1 - y2) === 2) || (y1 === y2 && Math.abs(x1 - x2) === 2)) tags.push({ t: 'opposition' });
      }
    }

    // 开局里的三种毛病（这步没吃子、没将军、没有战术目的时才算）
    if (!m.cap && !m.check && !tags.some((x) => ['fork', 'threat', 'pin', 'skewer', 'discovered', 'rescue', 'escapeCheck', 'defend'].includes(x.t))) {
      // 马走到边线
      if (m.piece === 'n' && phase !== 'endgame' && 'ah'.includes(m.to[0]) && !'ah'.includes(m.from[0])) tags.push({ t: 'knightRim' });
      // 同一个轻子走第二次：它已经出过了，家里还有至少两个轻子没动
      if (phase === 'opening' && (m.piece === 'n' || m.piece === 'b') && m.from[1] !== home) {
        const homes = me === 'w' ? { b1: 'N', g1: 'N', c1: 'B', f1: 'B' } : { b8: 'n', g8: 'n', c8: 'b', f8: 'b' };
        if (Object.keys(homes).filter((s) => b[s] === homes[s]).length >= 2) tags.push({ t: 'sameTwice', piece: m.piece });
      }
      // 子挡在自己还没动的中心兵前面
      if (phase === 'opening' && m.piece !== 'p' && m.piece !== 'k') {
        const r3 = me === 'w' ? '3' : '6', r2 = me === 'w' ? '2' : '7';
        if ((m.to === 'd' + r3 || m.to === 'e' + r3) && b[m.to[0] + r2] === (me === 'w' ? 'P' : 'p')) tags.push({ t: 'blockPawn', piece: m.piece, file: m.to[0] });
      }
    }

    // 残局出王：王往棋盘中心走
    if (m.piece === 'k' && !m.castle && phase === 'endgame') {
      const edge = (s) => Math.max(Math.abs(sqXY(s)[0] - 3.5), Math.abs(sqXY(s)[1] - 3.5));
      if (edge(m.to) < edge(m.from)) tags.push({ t: 'kingActive' });
    }

    // 叠兵：用兵吃子之后，这条线上有了两个自己的兵
    if (m.piece === 'p' && m.cap && phase !== 'endgame' && [1, 2, 3, 4, 5, 6, 7, 8].filter((r) => a[m.to[0] + r] === myPawn).length >= 2) {
      tags.push({ t: 'doublePawns', file: m.to[0] });
    }

    return tags.sort((x, y) => TAG_ORDER.indexOf(x.t) - TAG_ORDER.indexOf(y.t));
  }

  // ---------- 着法显示 ----------
  const PN_EN = { p: 'pawn', n: 'knight', b: 'bishop', r: 'rook', q: 'queen', k: 'king' };

  // 口语着法：knight to f3 / bishop takes b5 with check / castles kingside
  function speakEn(m) {
    if (m.castle) return (m.castle === 'O-O' ? 'castles kingside' : 'castles queenside') + (m.check ? ' with check' : '');
    return `${PN_EN[m.piece]} ${m.cap ? 'takes' : 'to'} ${m.to}${m.promo ? ` promoting to a ${PN_EN[m.promo]}` : ''}${m.check ? ' with check' : ''}`;
  }

  // ---------- Commentary phrases: English (spoken style; clauses without final punctuation, joined by `join`) ----------
  const W_EN = {
    PN: PN_EN, move: speakEn, end: '.',
    list: (a) => a.join(' and '),
    tgt: (t) => (t.p === 'k' ? 'king' : `${PN_EN[t.p]} on ${t.sq}`),
    mat: (n) => ({ 1: 'a pawn', 2: 'two pawns', 3: 'a minor piece', 4: 'a minor piece and a pawn', 5: 'a rook', 6: 'a rook and a pawn', 8: 'a rook and a minor piece', 9: 'a queen' })[n] || `about ${n} pawns of material`,
    ST: { winning: 'winning', better: 'better for you', equal: 'equal', worse: 'worse for you', losing: 'lost' },
    join: {
      idea: ['. With this move, ', ', because ', '; this way '],
      badIdea: ['. '],
      more: [', and ', ', plus ', '; also, '],
      but: ['. However, ', '. Careful though: '],
      problem: ['. The problem is that ', '. Unfortunately, ', '. But '],
      better: ['. It was better to play ', '. The stronger move was ', '. The engine prefers '],
      why: [', because ', ', since '],
      whyMore: [' and '],
      tip: ['. Remember: ', '. A tip: ', '. Keep in mind: '],
    },
    heads: {
      mate: ['Checkmate! The game is {yours|won}', '{Beautiful|Lovely} finish, the king has nowhere to go'],
      missedMate: [(p) => `So close, you had mate in ${p.n} and let it slip`, (p) => `You missed a forced mate in ${p.n}`],
      mating: [(p) => `You've locked in the win, mate in ${p.n}`, (p) => `It's a forced mate, just ${p.n} more moves`],
      best: ["Your move matches the engine's top choice", "{Precise|Spot on}, that's the best move", 'You found the strongest move, {nice eye|well spotted}', '{Perfect|Flawless} choice'],
      excellent: ['{Excellent|Great} move, practically as good as the best', 'Very solid, the position stays healthy', 'Good move, no chances for your opponent'],
      good: ['Playable, but there was something better', 'Okay, if a little loose', 'Not wrong, just not the most precise'],
      inaccuracy: ["That's a bit inaccurate", 'That {slightly|somewhat} spoils things', 'A small slip that gives away some of your edge'],
      mistake: ["That's a mistake", '{Unfortunately|Sadly} this one costs you', 'Not a good move, the position got noticeably worse'],
      blunder: ['{Ouch|Oh no}, that was a blunder', 'That one hurts, and it may decide the game', "That's a serious error"],
    },
    evalDrop: [(p) => `, roughly ${p.d} pawns thrown away`, (p) => `, costing about ${p.d} pawns`],
    // 提一句棋盘上刚画的标注（mark = 颜色加形状，比如 green arrow、red arrows、yellow circle）；以 ", " 开头，接在刚说完的那句后面
    seeMark: [
      (p) => `, {shown|marked} by the ${p.mark}`, (p) => `, as the ${p.mark} I drew {makes clear|points out}`, (p) => `, see the ${p.mark} {I drew|on the board}`,
      (p) => `, which I've {drawn|marked} with the ${p.mark}`, (p) => `, that's the ${p.mark} on the board`, (p) => `, just look at the ${p.mark}`,
      (p) => `, I've marked it with the ${p.mark}`, (p) => `, follow the ${p.mark} {I drew|on the board}`, (p) => `, the ${p.mark} is what I mean`,
      (p) => `, I drew the ${p.mark} for exactly this`, (p) => `, you can see it from the ${p.mark}`, (p) => `, as you can tell from the ${p.mark}`,
      (p) => `, look where the ${p.mark} {points|sits}`, (p) => `, it's the ${p.mark} I put on the board`,
    ],
    escapeCheck: ['you first deal with the check', 'you answer the check'],
    castle: ['you castle in time, so your king is safe and the rooks are connected', 'you tuck the king into a safe corner and bring a rook toward the center'],
    promo: [(p) => `your pawn reaches the last rank and becomes a ${p.x}`, (p) => `your pawn promotes to a ${p.x}`],
    check: ['it also comes with check, so your opponent has to respond first', 'it gives check and keeps the initiative'],
    fork: [(p) => `your ${p.piece} attacks the ${p.targets} at the same time, a fork your opponent can't fully answer`, (p) => `your ${p.piece} hits the ${p.targets} at once, a {lovely|neat|sharp} fork`],
    pin: [(p) => `your ${p.piece} pins the ${p.pinned}, with the ${p.behind} right behind it, so it can't move`, (p) => `you pin the ${p.pinned} in front of the ${p.behind}`],
    skewer: [(p) => `your ${p.piece} skewers the ${p.front}, and once it moves the ${p.behind} behind it falls`, (p) => `you set up a skewer, with the ${p.front} and ${p.behind} on the same line`],
    discovered: [(p) => `moving this piece opens the line for your ${p.piece}, which now hits the ${p.target}, a discovered attack`, (p) => `you unleash a discovered attack, your ${p.piece} suddenly targets the ${p.target}`],
    defend: [(p) => `you protect the ${p.x}, which was under attack`, (p) => `you add a defender to the threatened ${p.x}`],
    threatWin: [(p) => `you're eyeing their ${p.obj}, which they'll lose if they ignore it`, (p) => `you create a threat, and if they don't react the ${p.obj} is gone`],
    threatGain: [(p) => `you create a threat, and if they don't react they lose ${p.mat}`],
    threatMate: [(p) => `there's a hidden mating threat, if they ignore it ${p.n === 1 ? "it's mate next move" : `it's mate in ${p.n}`}`, (p) => `you're threatening mate, so they must defend right away`],
    parry: [(p) => `you stop your opponent's plan of ${p.m} to ${p.what}`, (p) => `you neutralise the threat of ${p.m} in time`],
    sacrifice: [(p) => `it looks like you're giving up the ${p.x}, but you get real compensation, a brave sacrifice`, (p) => `you give up the ${p.x}, and although they can take it, the engine says the sacrifice is sound`],
    sacMate: [(p) => `you sacrifice the ${p.x}, and that is exactly what forces mate`, (p) => `you give up the ${p.x}, and taking it allows checkmate`],
    freeCapture: [(p) => `you pick up an undefended ${p.cap} for free`, (p) => `you grab a ${p.cap} that nobody was protecting`],
    recapture: [(p) => `you take the ${p.cap} back`, (p) => `you recapture the ${p.cap} in time`],
    winTrade: [(p) => `you trade your ${p.piece} for their more valuable ${p.cap}, a great deal`, (p) => `your ${p.piece} takes the ${p.cap}, and even if it's recaptured you come out ahead`],
    trade: [(p) => `you trade your ${p.piece} for their ${p.cap}, simplifying the position`, (p) => `you swap off the ${p.cap}s`],
    sacCap: [(p) => `you take the ${p.cap} with your ${p.piece}, inviting a recapture, a deliberate sacrifice`],
    sacCapBad: [(p) => `you gave your ${p.piece} for a ${p.cap}, which is a bad trade`],
    threat: [(p) => `your ${p.piece} attacks their ${p.target}, so they have to spend a move dealing with it`, (p) => `your ${p.piece} targets their ${p.target} and puts them on the defensive`],
    rescue: [(p) => `you move the threatened ${p.piece} to safety in time`, (p) => `you save the attacked ${p.piece} first`],
    develop: [(p) => `you bring the ${p.piece} off the back rank, exactly what the opening calls for`, (p) => `your ${p.piece} joins the game and becomes active`],
    developBad: [(p) => `you wanted to develop the ${p.piece}, which is the right idea, but it went to the wrong square`],
    center: ['you grab the center, which matters a lot in the opening and middlegame', 'you gain a foothold in the center and more room for your pieces'],
    centerBad: ['you fight for the center, a good idea at the wrong time'],
    passed: [(p) => `you push the passed pawn to rank ${p.rank}, and no enemy pawn can stop it`],
    openFile: ['your rook takes the open file, where rooks are strongest', 'your rook lands on an open file and can invade along it'],
    semiOpen: ['your rook moves to a half-open file and eyes the enemy pawn'],
    earlyQueen: ['bringing the queen out this early lets your opponent develop with tempo', 'the queen is out a bit early, and they can gain time by attacking it'],
    kingShield: ['this pushes a pawn in front of your king and weakens its shelter'],
    kingWalk: ['moving the king in the opening gives up castling rights'],
    knightRim: ['the knight on the edge controls far fewer squares', 'your knight is out of play on the side of the board'],
    sameTwice: [(p) => `you move your ${p.piece} a second time while other pieces are still at home`, (p) => `moving the ${p.piece} again costs a tempo you could have used to develop a new piece`],
    blockPawn: [(p) => `your ${p.piece} now blocks your own ${p.file}-pawn`, (p) => `the ${p.file}-pawn is stuck behind your ${p.piece} and cannot take part in the center`],
    quiet: [(p) => `you reposition your ${p.piece} and prepare your next plan`, (p) => `you quietly improve your ${p.piece}`],
    // 更专业的棋理：前哨、第七横线、叠车、后车同线、双象、侧翼出象、连车、给王留出气口、残局出王、多子时兑子、叠兵
    outpost: [(p) => `your ${p.piece} lands on an outpost, a square their pawns can never attack`, (p) => `you plant your ${p.piece} on an outpost, protected by your pawn and safe from theirs`],
    rook7th: ['your rook reaches the seventh rank, where rooks are at their most dangerous', 'you put a rook on the seventh rank'],
    doubleRooks: ['you double your rooks on the file', 'your rooks line up on the same file'],
    battery: ['you line up your queen and rook on the same file', 'your queen and rook form a battery on the file'],
    bishopPair: ['you give a knight for a bishop and keep the bishop pair', 'you win the bishop pair'],
    fianchetto: ['you fianchetto your bishop, putting it on the long diagonal', 'your bishop goes to the long diagonal behind its pawn'],
    connectRooks: ['you connect your rooks', 'your rooks now protect each other along the back rank'],
    luft: ['you give your king an escape square against back-rank mates', 'you make luft for your king'],
    kingActive: ['you bring your king toward the center, where it belongs in the endgame', 'your king becomes an active piece'],
    removeDefender: [(p) => `you remove the piece that was defending their ${p.target}`, (p) => `you capture the defender, and their ${p.target} is left hanging`],
    rookBehind: ['your rook gets behind the passed pawn, exactly where it belongs', 'you follow the rule that rooks belong behind passed pawns'],
    opposition: ['you take the opposition, so their king has to give way', 'your king takes the opposition, the key idea in king and pawn endings'],
    tradeAhead: ['you trade pieces while you are ahead in material, which is the right policy', 'you simplify while you are material up'],
    doublePawns: [(p) => `this capture doubles your pawns on the ${p.file}-file`, (p) => `you end up with doubled pawns on the ${p.file}-file`],
    oppMate: [(p) => `after this your opponent has mate in ${p.n}`],
    hanging: [(p) => `your ${p.x} is left unprotected, and ${p.m} simply wins it`, (p) => `your opponent has ${p.m}, winning your ${p.x} for free`],
    ignored: [(p) => `your opponent was already threatening ${p.m} to ${p.what}, and this move doesn't deal with it`, (p) => `the threat of ${p.m} went unanswered`],
    replyCheck: [(p) => `your opponent can hit back with ${p.m}, and the initiative passes to them`],
    replyBest: [(p) => `your opponent's best reply is ${p.m}`, (p) => `you need to watch out for ${p.m}`],
    replyWhy: [(p) => `your opponent can reply ${p.m}, ${p.what}`, (p) => `next, your opponent has ${p.m}, ${p.what}`],
    oppWhat: {
      fork: (p) => `forking your ${p.targets}`, discovered: (p) => `with a discovered attack on your ${p.target}`, skewer: (p) => `skewering your ${p.front} and ${p.behind}`,
      pin: (p) => `pinning your ${p.pinned}`, threat: (p) => `attacking your ${p.target}`, winTrade: (p) => `trading their ${p.piece} for your more valuable ${p.cap}`,
      freeCapture: (p) => `winning your ${p.cap} for free`,
    },
    lineLose: [(p) => `, and down that road you lose ${p.mat}`, (p) => `, which ends up costing you ${p.mat}`],
    noPunish: [". You don't lose material right away, but your pieces end up worse placed", '. The issue is positional, it misses a more active plan'],
    better: [(p) => p.m],
    alt: [(p) => `. The engine slightly prefers ${p.m}, but it's close`],
    why: (rs) => rs.join(' and '),
    reason: {
      freeCapture: (p) => `it wins the undefended ${p.cap}`, recapture: (p) => `it takes the ${p.cap} back`, winTrade: (p) => `it trades your ${p.piece} for their more valuable ${p.cap}`,
      trade: (p) => `it trades off their ${p.cap}`, fork: (p) => `it forks the ${p.targets}`, pin: (p) => `it pins the ${p.pinned}`,
      skewer: (p) => `it skewers the ${p.front} and ${p.behind}`, discovered: (p) => `it unleashes a discovered attack on the ${p.target}`, threat: (p) => `it attacks the ${p.target}`,
      rescue: (p) => `it saves the threatened ${p.piece}`, defend: (p) => `it protects the threatened ${p.x}`, develop: () => 'it develops another piece', center: () => 'it strengthens your grip on the center',
      passed: () => 'it pushes the passed pawn', openFile: () => 'it puts a rook on the open file', check: () => 'it gives check and seizes the initiative', castle: () => 'it gets the king to safety first',
      promo: (p) => `it promotes to a ${p.x}`, bestParry: (p) => `it stops the threat of ${p.m}`,
      removeDefender: (p) => `it removes the defender of the ${p.target}`, rookBehind: () => 'it puts the rook behind the passed pawn', opposition: () => 'it takes the opposition',
      outpost: () => 'it puts a knight on an outpost', rook7th: () => 'it brings a rook to the seventh rank', doubleRooks: () => 'it doubles the rooks on the file',
      battery: () => 'it lines up queen and rook on the file', bishopPair: () => 'it wins the bishop pair', fianchetto: () => 'it fianchettoes the bishop onto the long diagonal',
      connectRooks: () => 'it connects the rooks', luft: () => 'it gives the king an escape square', kingActive: () => 'it activates the king',
      tradeAhead: () => 'it trades pieces while you are ahead',
    },
    bestGain: [(p) => `, and it would net you ${p.mat}`, (p) => `, coming out ${p.mat} ahead`],
    trend: [(p) => `. Overall, the position went from ${p.from} to ${p.to}`, (p) => `. It was ${p.from}, and now it's ${p.to}`],
    doomed: [(p) => `. Sadly the position can't be saved, your opponent has mate in ${p.n}`, (p) => `. The game is lost though, mate in ${p.n} is coming`],
    // 知识库查到的内容（自成一句，以句号开头）：开局名称、基本残局的结论
    opening: [(p) => `. This is the ${p.opening}`, (p) => `. You are now in the ${p.opening}`],
    endgameWin: [(p) => `. You have reached ${p.eg}, which is a theoretical win`, (p) => `. This is ${p.eg}, a known win with correct play`],
    endgameDraw: [(p) => `. This is ${p.eg}, which is a theoretical draw`, (p) => `. With ${p.eg} on the board, nobody can force mate`],
    // 术语讲解（自成一句）：某个术语在这次打开页面后第一次讲到时，补一句它是什么意思
    principle: {
      knightRim: ['. A knight on the rim is dim, as the old saying goes'],
      sameTwice: ['. A basic opening rule is not to move the same piece twice before the others are out'],
      blockPawn: ['. Pieces should not block the center pawns before those pawns have moved'],
      earlyQueen: ['. The opening rule is minor pieces before the queen'],
      kingWalk: ['. A king that has moved can no longer castle'],
    },
    mate: {
      backRank: ['. This is a back-rank mate, the king is trapped behind its own pawns'],
      smothered: ['. This is a smothered mate, the king is boxed in by its own pieces'],
      scholar: [". This is the Scholar's Mate, queen and bishop combine against the f-pawn"],
      support: ['. This is a support mate, the queen stands next to the king and is protected'],
    },
    define: {
      fork: ['. A fork is one piece attacking two targets at once'],
      pin: ['. A pin means a piece cannot move without exposing something more valuable behind it'],
      skewer: ['. A skewer attacks a valuable piece that has to move and expose the one behind it'],
      discovered: ['. A discovered attack happens when one piece moves away and uncovers an attack from another'],
      outpost: ['. An outpost is a square protected by your pawn that enemy pawns can never attack'],
      removeDefender: ['. Removing the defender means capturing the piece that protects something else'],
      rookBehind: ['. Rooks belong behind passed pawns, your own or the enemy\'s'],
      opposition: ['. The opposition means the kings face each other with one square between, and the side that does not have to move holds it'],
      fianchetto: ['. A fianchetto develops the bishop to the long diagonal, behind the knight pawn'],
      luft: ['. Luft is an escape square for the king, made by pushing a pawn in front of it'],
      battery: ['. A battery is two heavy pieces lined up on the same file'],
      passed: ['. A passed pawn has no enemy pawns in front of it or on the neighboring files'],
      openFile: ['. An open file is a file with no pawns on it'],
      bishopPair: ['. The bishop pair means you still have both bishops and your opponent does not'],
      rook7th: ['. A rook on the seventh rank attacks pawns from the side and cuts off the king'],
    },
    tails: {
      winning: ['. Keep it up and simplify, the win is close', '. Victory is in sight, just bring it home', ". You're way ahead, don't give them counterplay"],
      better: [". You've got the upper hand, keep pressing", '. The edge is yours, stay patient', '. Nice position, look for ways to grow the advantage'],
      equal: ['. Still balanced, keep looking for chances', '. Evenly matched', '. An equal fight, patience will decide it'],
      worse: ['. Slightly behind, but that was a good defensive move', ". Not a great position, but you're fighting hard"],
      losing: [". It's tough, but that was the most stubborn defense", ". Don't give up, keep making it hard for them"],
    },
    tipHanging: ['before every move, check that each of your pieces is protected', 'build a blunder-check habit and ask whether your opponent can capture anything after your move'],
    tipKing: ['before moving, look around your king for checks and mating ideas'],
    tipTactic: ['scan their checks, captures and threats before every move', 'watch for squares where one enemy piece could attack two of yours'],
    tipMissedMate: ['when the enemy king is short of squares, look at every check first', 'always examine checks before anything else, one of them may be mate'],
    tipThreat: ["before every move, ask what your opponent's last move wants", "check their threats before your own attack, their last move usually has a purpose"],
    tips: {
      opening: ['develop your pieces, control the center and castle early', "avoid moving the same piece twice before you've developed the rest", "don't rush to grab pawns or bring out the queen, development comes first"],
      middlegame: ['look for checks, captures and threats before every move', 'keep every piece protected, loose pieces drop off', 'find a weakness in their camp first, then aim your pieces at it'],
      endgame: ['in the endgame the king is a fighting piece, so activate it', 'passed pawns are gold in the endgame, so calculate the races', 'rooks belong behind passed pawns, yours or theirs'],
    },
    whatMate: 'deliver mate', whatCapMine: (x) => `win your ${x}`, whatMat: (m) => `win ${m}`,
  };

  // ---------- 候选理由：这步（或推荐着法）为什么好/坏，由网络挑选、排序 ----------
  const pv9 = (p) => (p === 'k' ? 1 : VAL[p] / 9);
  const WARN = ['earlyQueen', 'kingShield', 'kingWalk'];

  // 对方威胁的内容（用于“对方本来想走 X，……”）：将杀 / 吃掉你的某个子 / 赢得多少子力
  function threatWhat(t, W) {
    if (t.mate) return W.whatMate;
    if (t.m.cap) return W.whatCapMine(W.tgt({ p: t.m.cap, sq: t.m.to }));
    return W.whatMat(W.mat(Math.max(1, Math.round(t.gain))));
  }

  function tagParams(t, W) {
    const P = W.PN;
    return {
      piece: P[t.piece], cap: P[t.cap], rank: t.rank, file: t.file,
      target: t.target && W.tgt(t.target), x: t.target && W.tgt(t.target),
      targets: t.targets && W.list(t.targets.map(W.tgt)),
      pinned: t.pinned && W.tgt(t.pinned), front: t.front && W.tgt(t.front), behind: t.behind && W.tgt(t.behind),
    };
  }

  function tagMag(t) {
    switch (t.t) {
      case 'fork': return Math.max(...t.targets.map((x) => pv9(x.p)));
      case 'threat': case 'discovered': case 'defend': return pv9(t.target.p);
      case 'pin': return pv9(t.pinned.p) + (t.behind.p === 'k' ? 0.2 : 0);
      case 'skewer': return pv9(t.behind.p);
      case 'freeCapture': case 'recapture': return pv9(t.cap);
      case 'winTrade': return (VAL[t.cap] - VAL[t.piece]) / 9;
      case 'rescue': return pv9(t.piece);
      case 'passed': return t.rank / 8;
      case 'removeDefender': return pv9(t.target.p);
      case 'outpost': case 'rook7th': case 'bishopPair': case 'tradeAhead': case 'rookBehind': case 'opposition': return 0.3;
      case 'doubleRooks': case 'battery': case 'kingActive': return 0.25;
      case 'fianchetto': case 'connectRooks': case 'luft': return 0.2;
      default: return 0.1;
    }
  }

  // 这步棋的理由：规则识别（双击、牵制、闪击…）+ 威胁分析（这步在瞄准什么、化解了什么威胁）
  // “这步的意图”只说在瞄准什么，不说出下一步该怎么走
  // 新加的棋理在“选哪条理由”的网络眼里，算作它已经认识的相近类型（网络只管挑哪条说，说什么由 tag 决定）
  const STYPE = { outpost: 'develop', fianchetto: 'develop', connectRooks: 'develop', rook7th: 'openFile', doubleRooks: 'openFile', battery: 'openFile',
    bishopPair: 'trade', tradeAhead: 'trade', luft: 'defend', kingActive: 'center', doublePawns: 'kingShield',
    removeDefender: 'threat', rookBehind: 'openFile', opposition: 'center', knightRim: 'earlyQueen', sameTwice: 'earlyQueen', blockPawn: 'earlyQueen' };

  function playedReasons(c, W) {
    const P = W.PN, bad = BAD.includes(c.kind), p = c.played, out = [];
    if (!p || c.kind === 'mate') return out;
    if (p.castle) out.push({ type: 'castle', key: 'castle', mag: 0.3 });
    if (p.promo) out.push({ type: 'promo', key: 'promo', p: { x: P[p.promo] }, mag: pv9(p.promo) });
    for (const t of c.tags) {
      if (t.t === 'earlyQueen' && !bad && c.kind !== 'good') continue;
      if (t.t === 'kingShield' && c.loss < 2) continue;
      if (['knightRim', 'sameTwice', 'blockPawn'].includes(t.t) && !bad && c.kind !== 'good') continue; // 走得好就不挑开局原则上的毛病
      if (t.t === 'sacCap' && c.sacrifice) continue;
      if (t.t === 'freeCapture' && c.oppMateAfter) continue;              // 吃到的子已经无关紧要
      if ((t.t === 'rescue' || t.t === 'defend') && c.parried) continue;  // “化解威胁”说得更具体
      if (t.t === 'threat' && c.myThreat) continue;                       // “在瞄准什么”说得更具体
      if (t.t === 'doublePawns' && !bad && c.kind !== 'good') continue;   // 好棋里的叠兵是值得的代价，不挑这个毛病
      if (t.t === 'develop' && c.tags.some((x) => x.t === 'fianchetto')) continue; // “侧翼出象”说得更具体
      if (t.t === 'trade' && c.tags.some((x) => x.t === 'tradeAhead' || x.t === 'bishopPair')) continue;
      if (bad && STYPE[t.t] && !WARN.includes(STYPE[t.t])) continue;           // 走坏了就别夸这些局面上的好处
      const key = bad && ['develop', 'center', 'sacCap'].includes(t.t) ? t.t + 'Bad' : t.t; // 走坏了就别夸
      out.push({ type: STYPE[t.t] || t.t, tag: t.t, key, p: tagParams(t, W), mag: tagMag(t) });
    }
    if (p.check) out.push({ type: 'check', key: 'check', mag: 0.2 });
    if (c.myThreat) {
      const t = c.myThreat;
      if (t.mate) out.push({ type: 'threatMate', key: 'threatMate', p: { n: t.mate }, mag: 1, mate: 1 });
      else if (t.m.cap) out.push({ type: 'threatWin', key: 'threatWin', p: { obj: W.tgt({ p: t.m.cap, sq: t.m.to }) }, mag: Math.min(t.gain, 9) / 9 });
      else out.push({ type: 'threatWin', key: 'threatGain', p: { mat: W.mat(Math.max(1, Math.round(t.gain))) }, mag: Math.min(t.gain, 9) / 9 });
    }
    if (c.parried) {
      const t = c.oppThreat;
      out.push({ type: 'parry', key: 'parry', p: { m: W.move(t.m), what: threatWhat(t, W) }, mag: t.mate ? 1 : Math.min(t.gain, 9) / 9, mate: t.mate ? 1 : 0 });
    }
    if (c.sacrifice) out.push({ type: 'sacrifice', key: c.mateAfter ? 'sacMate' : 'sacrifice', p: { x: P[c.reply.cap] }, mag: pv9(c.reply.cap), mate: c.mateAfter ? 1 : 0 });
    return out;
  }

  // 推荐着法为什么更好（短句，接在“其实更好的是 X，因为……”后面）
  function bestReasons(c, W) {
    const P = W.PN, bm = c.best, out = [];
    for (const t of c.bestTags) {
      if (!W.reason[t.t] || t.t === 'escapeCheck') continue;
      out.push({ type: STYPE[t.t] || t.t, tag: t.t, p: tagParams(t, W), text: W.reason[t.t](tagParams(t, W)), mag: tagMag(t) });
    }
    if (bm.castle) out.push({ type: 'castle', p: {}, text: W.reason.castle(), mag: 0.3 });
    if (bm.promo) out.push({ type: 'promo', p: { x: P[bm.promo] }, text: W.reason.promo({ x: P[bm.promo] }), mag: pv9(bm.promo) });
    if (c.oppThreat && !c.parried) {
      const t = c.oppThreat;
      out.push({ type: 'bestParry', p: { m: W.move(t.m) }, text: W.reason.bestParry({ m: W.move(t.m) }), mag: t.mate ? 1 : Math.min(t.gain, 9) / 9, mate: t.mate ? 1 : 0 });
    }
    return out;
  }

  // ---------- 把分析结果说成一段连贯的话（像老师当面讲，不分段；说法、连接词、理由的取舍和顺序由网络 S 决定） ----------
  // 把一段讲解一句句接起来。每接上一句、语言模型每生成一个词，都会通过 S.emit 把“到目前为止的全文”报出去
  // （连同其中已经定下来、不会再改的长度——正在生成的那一句有可能被推翻重写）：
  // 讲解在后台线程里生成时，面板就靠它一边生成一边显示、一边朗读（没有 S.emit 时只是普通的拼接）。
  function makeTalk(W, S) {
    const lead = (x) => (/^[A-Za-z0-9]/.test(x) ? ' ' + x : x); // 片段之间补空格
    const tidy = (x) => x.replace(/\s+/g, ' ').trim().replace(/(^|[.!?]\s+)([a-z])/g, (m, a, b) => a + b.toUpperCase()); // 空白收拢；句首大写
    const emit = (x, solid) => { if (S.emit) S.emit(tidy(x), tidy(solid).length); };
    const todo = []; // 要说的话先按顺序排好，最后由 done() 一句句生成（网络在显卡上跑时，每个词都要等结果，所以生成是异步的）
    const put = (x) => { talk.text += lead(x); emit(talk.text, talk.text); };
    const talk = {
      text: '',
      part() { const base = talk.text; return S.emit ? (x) => emit(base + lead(x), base) : undefined; }, // 正在生成的这一句：接在已说的话后面报出去
      add(x) { todo.push(() => x); },             // 一段现成的话
      later(f) { todo.push(f); },                  // 轮到时再生成的一段话（f 返回文字）
      say(key, p) { const pool = key.split('.').reduce((o, k) => o[k], W); todo.push(() => S.pick(key, pool, p || {}, talk.part())); },
      async done() { // 按顺序生成全部，收尾补句号
        for (const f of todo) put(await f());
        const t = tidy(talk.text);
        return /[.!?]$/.test(t) ? t : t + W.end;
      },
    };
    return talk;
  }

  // 把一条战术在棋盘上标出来（标注工具）：at 格子上的子在攻击谁，就画箭头过去；被牵制、被串击、被闪击、被保护的子圈出来
  function markTag(t, at, color, S, note) {
    const to = (sq, n) => S.tool('board_arrow', { from: at, to: sq, color, note: note || n });
    const ring = (sq, n, col) => S.tool('board_circle', { square: sq, color: col || color, note: note || n });
    if (t.t === 'fork') t.targets.forEach((x) => to(x.sq, 'attacked'));
    else if (t.t === 'threat') to(t.target.sq, 'attacked');
    else if (t.t === 'pin') { to(t.behind.sq, 'pin'); ring(t.pinned.sq, 'pinned'); }
    else if (t.t === 'skewer') { to(t.behind.sq, 'skewer'); ring(t.front.sq, 'has to move'); }
    else if (t.t === 'discovered') ring(t.target.sq, 'attacked');
    else if (t.t === 'defend') ring(t.target.sq, 'protected', 'green');
    else if (t.t === 'removeDefender') ring(t.target.sq, 'attacked');
  }

  function compose(c, W, S) {
    const P = W.PN, mv = W.move, bad = BAD.includes(c.kind);
    const talk = makeTalk(W, S), say = talk.say;

    // 评价
    say('heads.' + c.kind, { n: c.kind === 'missedMate' ? c.mateBefore : c.mateAfter });
    if (c.kind === 'mate' && c.matePattern) say('mate.' + c.matePattern); // 有名字的将杀：说出它叫什么
    if (['mistake', 'blunder'].includes(c.kind) && c.cpB != null && c.cpA != null && c.cpB - c.cpA >= 0.3) {
      say('evalDrop', { d: (c.cpB - c.cpA).toFixed(1) });
    }

    // 这步的想法：只讲最重要的 1 条理由（由网络挑）
    const rs = playedReasons(c, W);
    const chosen = rs.length ? S.select(rs, 1, 0, W) : [];
    chosen.forEach((r, i) => {
      // 好棋才用“这样做 / 因为”接上；“还行”和坏棋前面是在挑毛病，断句另起一句
      const conn = WARN.includes(r.type) ? 'join.but' : i === 0 ? (bad || c.kind === 'good' ? 'join.badIdea' : 'join.idea') : 'join.more';
      say(conn);
      say(r.key, r.p);
    });
    if (!chosen.length && !bad && c.kind !== 'good' && c.kind !== 'mate' && c.played) { say('join.idea'); say('quiet', { piece: P[c.played.piece] }); } // “还行”后面紧接着讲更好的走法，不用凑一句

    // 在棋盘上标出来（用标注工具）：好棋标挑中的那条理由；坏棋在下面标对手怎么惩罚（红）、本来该怎么走（绿）
    const arrow = (m, color, note) => m && S.tool('board_arrow', { from: m.from, to: m.to, color, note });
    const ring = (sq, color, note) => S.tool('board_circle', { square: sq, color, note });
    // 说一句“见我画的红箭头 / 绿圈”：指的是从第 from 次工具调用起、这种颜色的标注（有箭头说箭头，否则说圈；不止一个用复数）
    const seeMark = (from, color) => {
      const ms = S.toolLog.slice(from).map((t) => t.result).filter((r) => r && r.draw && r.color === color);
      const shape = ms.some((r) => r.draw === 'arrow') ? 'arrow' : 'circle', n = ms.filter((r) => r.draw === shape).length;
      if (n) say('seeMark', { mark: `${color} ${shape}${n > 1 ? 's' : ''}` });
    };
    let at = S.toolLog.length;
    if (!bad && c.played) {
      const first = chosen[0] && c.tags.find((x) => x.t === chosen[0].tag);
      if (first) markTag(first, c.played.to, 'yellow', S); // 网络挑中的那条理由先标
      c.tags.filter((x) => x !== first && ['fork', 'pin', 'skewer', 'discovered', 'threat'].includes(x.t)).forEach((x) => markTag(x, c.played.to, 'yellow', S)); // 这步同时做到的其他战术
      if (c.myThreat && c.myThreat.m.cap) ring(c.myThreat.m.to, 'yellow', 'target'); // 只圈目标，不画出下一步怎么走
      if (c.parried) { arrow(c.oppThreat.m, 'blue', 'stopped'); if (c.oppThreat.m.cap) ring(c.oppThreat.m.to, 'green', 'saved'); } // 化解掉的威胁
      if (chosen[0]) seeMark(at, chosen[0].type === 'parry' ? (c.oppThreat.m.cap ? 'green' : 'blue') : 'yellow');
    }
    // 对手的惩罚：他的应着（红箭头）、吃到的子和这步攻击的子（红）；如果是先威胁再吃子，把接下来吃子的那步也画出来
    const punish = (m, tag, mating) => {
      arrow(m, 'red', 'reply');
      if (m.cap) ring(m.to, 'red', 'lost');
      if (tag) markTag(tag, m.to, 'red', S);
      const next = c.replyLine.moves[2];
      if (next && (mating || (!m.cap && next.cap))) { arrow(next, 'red', mating ? 'mate' : 'wins'); if (next.cap) ring(next.to, 'red', 'lost'); }
    };
    if (bad && c.played) arrow(c.played, 'orange', 'your move'); // 走错的这一步

    // 知识（都是用查询工具从知识库查来的）：第一次讲到某个术语时解释一句；这步走进了有名字的开局、或者进入基本残局时提一句
    if (c.kind !== 'mate') {
      const term = !bad && chosen[0] && S.tool('glossary_lookup', { term: chosen[0].tag || chosen[0].type });
      if (term && !S.known.has(term.entry)) { say('define.' + term.entry); S.learned.push(term.entry); }
      // 挑的是开局里的毛病：第一次讲到时补一句它背后的原则
      const rule = chosen[0] && WARN.includes(chosen[0].type) && S.tool('principle_lookup', { topic: chosen[0].tag || chosen[0].type });
      if (rule && !S.known.has('rule:' + rule.entry)) { say('principle.' + rule.entry); S.learned.push('rule:' + rule.entry); }
      if (c.opening) say('opening', { opening: c.opening });
      if (c.endgame) say(c.endgame.verdict === 'win' ? 'endgameWin' : 'endgameDraw', { eg: c.endgame.name });
    }

    // 问题在哪
    if (bad && (c.oppMateAfter || c.reply)) say('join.problem');
    if (bad && c.oppMateAfter) {
      say('oppMate', { n: c.oppMateAfter });
      if (c.reply) punish(c.reply, null, true);
      const king = Object.keys(c.played.after).find((sq) => c.played.after[sq] === (c.me === 'w' ? 'K' : 'k'));
      if (king) ring(king, 'red', 'king in danger');
      seeMark(at, 'red');
      if (c.matePattern) say('mate.' + c.matePattern);
    } else if (bad && c.reply) {
      if (c.hanging) { say('hanging', { m: mv(c.reply), x: P[c.reply.cap] }); punish(c.reply); }
      else if (c.ignored) { say('ignored', { m: mv(c.oppThreat.m), what: threatWhat(c.oppThreat, W) }); arrow(c.oppThreat.m, 'red', 'threat'); if (c.oppThreat.m.cap) ring(c.oppThreat.m.to, 'red', 'lost'); }
      else {
        // 对手的回应有明确目的时，用一句话讲清楚它要干什么
        const rt = ['fork', 'discovered', 'skewer', 'pin', 'threat', 'winTrade', 'freeCapture'].map((k) => c.replyTags.find((x) => x.t === k)).find(Boolean);
        if (rt) say('replyWhy', { m: mv(c.reply), what: W.oppWhat[rt.t](tagParams(rt, W)) });
        else if (c.reply.check) say('replyCheck', { m: mv(c.reply) });
        else say('replyBest', { m: mv(c.reply) });
        punish(c.reply, rt);
      }
      seeMark(at, 'red');
      if (c.playedGain <= -1) say('lineLose', { mat: W.mat(-c.playedGain) });
    }

    // 更好的下法（这步本来可以怎么走——是对已走过这步的讲解，不是建议下一步）
    if (c.best && (bad || c.kind === 'good')) {
      const brs = bestReasons(c, W);
      const why = brs.length ? S.select(brs, 1, 1, W) : [];
      say('join.better');
      say('better', { m: mv(c.best) });
      at = S.toolLog.length;
      arrow(c.best, 'green', 'better'); // 更好的走法，以及它能做到什么
      seeMark(at, 'green');
      const bt = why[0] && c.bestTags.find((x) => x.t === why[0].tag);
      if (bt) markTag(bt, c.best.to, 'green', S, 'better');
      else if (c.best.cap) ring(c.best.to, 'green', 'better');
      if (why.length) {
        say('join.why');
        talk.later(async () => {
          const out = [];
          for (const r of why) out.push((await S.gen('reason.' + (r.tag || r.type), r.p, talk.part())) || r.text);
          return W.why(out);
        });
      }
      if (c.bestGain >= 1 && c.bestGain > c.playedGain) say('bestGain', { mat: W.mat(c.bestGain) });
    }

    // 局势与建议：只在要紧时说（大势已去；失误和大漏着后给一句针对性的建议）
    if (c.kind !== 'mate') {
      if (!bad && c.oppMateAfter) say('doomed', { n: c.oppMateAfter });
      if (['mistake', 'blunder', 'missedMate'].includes(c.kind)) {
        const tip = c.kind === 'missedMate' ? 'tipMissedMate' : c.hanging ? 'tipHanging' : c.ignored ? 'tipThreat' : c.oppMateAfter || (c.reply && c.reply.check) ? 'tipKing'
          : c.replyTags.some((x) => ['fork', 'pin', 'skewer', 'discovered'].includes(x.t)) ? 'tipTactic' : 'tips.' + c.phase;
        say('join.tip');
        say(tip);
      }
    }

    return talk.done().then((text) => [{ text }]);
  }

  // ---------- 选词/选句/选理由神经网络 ----------
  // 输入 = 局面特征(33) + 候选特征(62)，5 层 tanh 隐藏层（2368→1760→880→440→220），输出一个分数，共约 643 万个参数。
  // 同一组候选（几种说法 / 几个词 / 说或不说 / 几条理由加“到此为止”）按分数做 softmax 抽样。
  // 权重是离线训练好直接写在 NN_W 里的（训练：train-nn.js + nn/；按行 int8 量化 + base64），浏览器里只做推理。
  const KINDS = ['mate', 'mating', 'missedMate', 'best', 'excellent', 'good', 'inaccuracy', 'mistake', 'blunder'];
  const PHASES = ['opening', 'middlegame', 'endgame'];
  const CATS = ['head', 'idea', 'problem', 'next', 'better', 'outlook', 'word', 'include', 'reason'];
  const INC = ['evalKeep', 'extraTag', 'check', 'line', 'noPunish', 'bestLine', 'alt', 'tail', 'tip', 'next'];
  const RTYPES = ['escapeCheck', 'castle', 'promo', 'check', 'fork', 'pin', 'skewer', 'discovered', 'threatMate', 'threatWin',
    'parry', 'sacrifice', 'freeCapture', 'recapture', 'winTrade', 'trade', 'sacCap', 'threat', 'rescue', 'defend',
    'develop', 'center', 'passed', 'openFile', 'semiOpen', 'earlyQueen', 'kingShield', 'kingWalk', 'bestParry', 'stop'];
  const CTX_DIM = 33, CAND_DIM = 62, N_IN = CTX_DIM + CAND_DIM, NN_T = 0.6;
  const NN_LAYERS = [N_IN, 2368, 1760, 880, 440, 220, 1];
  const POS_WORDS = ['good', 'great', 'nice', 'excellent', 'best', 'precise', 'solid', 'brave', 'beautiful', 'lovely', 'perfect', 'flawless', 'spot on', 'well', 'neat', 'sharp'];
  const NEG_WORDS = ['mistake', 'blunder', 'ouch', 'oh no', 'careful', 'danger', 'problem', 'lose', 'lost', 'worse', 'wrong', 'slip', 'hurts', 'unfortunately', 'sadly', 'missed', 'spoils'];
  const MOVE_RE1 = /\b(pawn|knight|bishop|rook|queen|king) (to|takes) [a-h][1-8]|castles/i;
  const hits = (t, list) => { const l = t.toLowerCase(); return list.reduce((n, w) => n + (l.includes(w) ? 1 : 0), 0); };
  const stripSlots = (t) => t.replace(/\{([^{}|]*)[^{}]*\}/g, '$1');

  function bigrams(t) {
    const s = new Set();
    for (let i = 0; i < t.length - 1; i++) s.add(t.slice(i, i + 2));
    return s;
  }
  function simTo(list, t) {
    const a = bigrams(t);
    let best = 0;
    for (const u of list) {
      const b = bigrams(u);
      let n = 0;
      for (const x of a) if (b.has(x)) n++;
      best = Math.max(best, n / Math.max(1, a.size + b.size - n));
    }
    return best;
  }

  function catOf(key) {
    const k = key.split('.')[0];
    if (k === 'join') return 'word';
    if (k === 'heads' || k === 'evalDrop' || k === 'evalKeep') return 'head';
    if (['oppMate', 'hanging', 'ignored', 'replyCheck', 'replyBest', 'replyWhy', 'line', 'lineLose', 'noPunish', 'hanging4', 'reply4', 'mated4'].includes(k)) return 'problem';
    if (['nextPlan', 'nextReply', 'mateRoute'].includes(k)) return 'next';
    if (['better', 'alt', 'bestLine', 'bestGain'].includes(k)) return 'better';
    if (['trend', 'tails', 'tipHanging', 'tipKing', 'tipThreat', 'tips', 'doomed', 'opening', 'endgameWin', 'endgameDraw', 'define'].includes(k)) return 'outlook';
    return 'idea';
  }

  const threatMag = (t) => (t ? (t.mate ? 1 : Math.min(t.gain, 9) / 9) : 0);

  // 局面特征：评级、阶段、局势、损失、胜率、送子/弃子/被杀/杀棋/将军/吃子、特点数量、双方威胁
  function ctxVec(c) {
    const v = new Float32Array(CTX_DIM);
    v[KINDS.indexOf(c.kind)] = 1;
    v[9 + PHASES.indexOf(c.phase)] = 1;
    v[12 + ORDER.indexOf(c.stAfter)] = 1;
    v[17] = Math.min(c.loss, 60) / 30;
    v[18] = c.wa / 100;
    v[19] = BAD.includes(c.kind) ? 1 : 0;
    v[20] = c.hanging ? 1 : 0;
    v[21] = c.sacrifice ? 1 : 0;
    v[22] = c.oppMateAfter ? 1 : 0;
    v[23] = c.mateAfter ? 1 : 0;
    v[24] = c.played && c.played.check ? 1 : 0;
    v[25] = c.played && c.played.cap ? 1 : 0;
    v[26] = Math.min(c.tags.length, 3) / 3;
    v[27] = 1; // 保留位（以前用来区分语言）
    v[28] = c.oppThreat ? 1 : 0;
    v[29] = threatMag(c.oppThreat);
    v[30] = c.myThreat ? 1 : 0;
    v[31] = threatMag(c.myThreat);
    v[32] = c.parried ? 1 : 0;
    return v;
  }

  // 候选特征：段落、可选句、说/不说、长度、褒贬、感叹、着法、数字、最近用过、相似度；
  // 理由另有：理由类型、分量（能赢多少子）、是否涉及杀棋、属于这步还是推荐着法、已经说了几条
  function candFeat(cat, slot, text, recent, sim, say, r) {
    const f = new Float32Array(CAND_DIM);
    f[CATS.indexOf(cat)] = 1;
    if (slot) f[9 + INC.indexOf(slot)] = 1;
    f[19] = say;
    f[20] = Math.min(text.length, 160) / 110;
    f[21] = hits(text, POS_WORDS) / 3;
    f[22] = hits(text, NEG_WORDS) / 3;
    f[23] = /[!！]/.test(text) ? 1 : 0;
    f[24] = MOVE_RE1.test(text) ? 1 : 0;
    f[25] = /\d/.test(text) ? 1 : 0;
    f[26] = Math.min(recent, 4) / 2;
    f[27] = sim;
    if (r) {
      f[28 + RTYPES.indexOf(r.type)] = 1;
      f[58] = Math.min(r.mag || 0, 1.2);
      f[59] = r.mate ? 1 : 0;
      f[60] = r.subj;
      f[61] = r.order / 3;
    }
    return f;
  }

  // 两个网络的权重都不写在脚本里：训练脚本把它们写到 model/ 文件夹，上传到 GitHub 后，插件运行时下载（主线程下载，交给后台线程）。
  // 离线工具（Node）里由 tools/model.js 读进来放在 globalThis.COACH_MODEL。
  const COACH_W0 = (typeof globalThis !== 'undefined' && globalThis.COACH_MODEL) || {};
  let NN_W = COACH_W0.nn || null;
  function setModel(m) {
    if (m.nn) { NN_W = m.nn; NET = null; }
    if (m.lm) { LM = m.lm; LMN = null; LMCPU = null; }
  }

  // 解码权重：每层的 W、b 是 Int16 的 base64，乘以各自的缩放系数还原成浮点数
  // 解码权重：每层 W 是 int8（按行各一个缩放系数 s），偏置 b 是 float32，都存成 base64
  function b64bytes(str) {
    const bin = atob(str), u8 = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) u8[i] = bin.charCodeAt(i);
    return u8;
  }
  var NET = null;
  function net() {
    if (!NET) {
      NET = NN_W.layers.map((l, k) => {
        const nIn = NN_LAYERS[k], nOut = NN_LAYERS[k + 1];
        const q = new Int8Array(b64bytes(l.W).buffer), sc = new Float32Array(b64bytes(l.s).buffer);
        const W = new Float32Array(nIn * nOut);
        for (let j = 0; j < nOut; j++) for (let i = 0; i < nIn; i++) W[j * nIn + i] = q[j * nIn + i] * sc[j];
        return { nIn, nOut, W, b: new Float32Array(b64bytes(l.b).buffer) };
      });
    }
    return NET;
  }

  // 第一层里“局面特征”那部分对同一条讲解的所有候选都一样：每条讲解只算一次
  function nnPre(cx) {
    const { W, b, nIn, nOut } = net()[0], pre = new Float32Array(nOut);
    for (let j = 0; j < nOut; j++) {
      let a = b[j];
      const off = j * nIn;
      for (let i = 0; i < CTX_DIM; i++) a += W[off + i] * cx[i];
      pre[j] = a;
    }
    return pre;
  }

  // 给一个候选打分：第一层只算候选特征里不为 0 的几项（大部分是 0/1 标记），后面几层照常
  function nnScore(pre, f) {
    const layers = net(), L0 = layers[0], nz = [];
    for (let i = 0; i < f.length; i++) if (f[i] !== 0) nz.push(i);
    let h = new Float32Array(L0.nOut);
    for (let j = 0; j < L0.nOut; j++) {
      let a = pre[j];
      const off = j * L0.nIn + CTX_DIM;
      for (const i of nz) a += L0.W[off + i] * f[i];
      h[j] = Math.tanh(a);
    }
    for (let l = 1; l < layers.length; l++) {
      const { W, b, nIn, nOut } = layers[l], o = new Float32Array(nOut);
      for (let j = 0; j < nOut; j++) {
        let a = b[j];
        const off = j * nIn;
        for (let i = 0; i < nIn; i++) a += W[off + i] * h[i];
        o[j] = l < layers.length - 1 ? Math.tanh(a) : a;
      }
      h = o;
    }
    return h[0];
  }

  function mulberry32(a) {
    return () => {
      a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function softmax(sc, T) {
    const m = Math.max(...sc), e = sc.map((x) => Math.exp((x - m) / T)), z = e.reduce((a, b) => a + b, 0);
    return e.map((x) => x / z);
  }

  // ---------- 逐词生成的语言模型（预测下一个词） ----------
  // 看前 K 个词 + 条件（这句要表达的“意思”、这步的评级、用第几组说法），算出下一个词的概率，一个词一个词往下写。
  // 棋子、格子、着法用占位词代替（⟨piece⟩、⟨m⟩……），写完再填进真实内容，所以具体事实不会说错；
  // 这句必须提到的内容没写全之前不许结束，用不到的占位词不许出现。
  // 权重离线训练好直接写在 LM 里（训练：train-lm.js + nn/），浏览器里只做推理。
  let LM = COACH_W0.lm || null; // 语言模型的权重：不写在脚本里了，运行时从 GitHub 下载（见“模型权重”一段），由 setModel 装进来
  const LM_TEMP = 0.7, LM_TOPK = 10, LM_TRIES = 6, LM_MINP = 0.15; // 概率不到最可能那个词 15% 的词不挑（接歪的搭配基本都在这以下）
  var LMN = null;

  // 通顺约束：每一步只允许“前两个词 + 这个词”在这种意思的语料里连着出现过的词。
  // 网络照样给每个词打分、按概率挑，把同一个意思的不同说法重新组合成新句子；但不会挑出语料里从没连在一起用过的搭配，
  // 也不会把别的意思的话接进来——不会冒出半截话，也不会把“亏了”说成“赚了”。
  const LM_CTX = 2;
  const lmCtxKey = (ctx, n, V) => { let k = 0; for (let i = ctx.length - n; i < ctx.length; i++) k = k * V + ctx[i]; return k; };
  function lmGuard(key) {
    const N = lmNet();
    if (!N.guard.has(key)) {
      let g = null;
      if (LM.seq && LM.seq[key]) {
        const s = new Uint16Array(b64bytes(LM.seq[key]).buffer), BOS = N.id.get('<bos>'), EOS = N.id.get('<eos>'), m = new Map();
        let ctx = new Array(LM_CTX).fill(BOS);
        for (const t of s) {
          const k = lmCtxKey(ctx, LM_CTX, N.V);
          let set = m.get(k);
          if (!set) m.set(k, (set = new Set()));
          set.add(t);
          if (t === EOS) ctx = new Array(LM_CTX).fill(BOS);
          else { ctx.shift(); ctx.push(t); }
        }
        g = new Map([...m].map(([k, set]) => [k, Int32Array.from(set)]));
      }
      N.guard.set(key, g);
    }
    return N.guard.get(key);
  }

  // 两个网络共用的东西：词表、条件表、通顺约束
  function lmNet() {
    if (!LMN && LM) {
      LMN = {
        K: LM.K, V: LM.vocab.length, bo: new Float32Array(b64bytes(LM.w.bo).buffer), nets: {},
        id: new Map(LM.vocab.map((t, i) => [t, i])), cid: new Map(LM.conds.map((c, i) => [c, i])),
        slots: LM.vocab.map((t, i) => (t.startsWith('⟨') ? i : -1)).filter((i) => i >= 0),
        guard: new Map(),
      };
    }
    return LMN;
  }

  // 权重只存了一份，里面是“大网络套着小网络”：小网络就是大网络每一层的前一部分（词向量的前几维、隐藏层的前几个单元），参数约 1/5。
  // full = 取完整的网络（有 WebGPU 时在显卡上跑）；否则只取出小网络（在 CPU 上跑）
  function lmModel(full) {
    const N = lmNet(), name = full ? 'full' : 'slim';
    if (!N.nets[name]) {
      const F = { D: LM.D, DC: LM.DC, H1: LM.H1, H2: LM.H2 }, S = full ? F : LM.S || F, K = LM.K;
      const seq = (n) => Int32Array.from({ length: n }, (_, i) => i);
      const cols1 = []; // 小网络在第一层用到的输入列：每个词向量的前 D 维 + 条件向量的前 DC 维
      for (let k = 0; k < K; k++) for (let d = 0; d < S.D; d++) cols1.push(k * F.D + d);
      for (let i = 0; i < S.DC; i++) cols1.push(K * F.D + i);
      const deq = (o, rows, colsFull, cols) => { // 取前 rows 行、指定的列，int8 × 这一行的比例 → 小数
        const q = new Int8Array(b64bytes(o.q).buffer), sc = new Float32Array(b64bytes(o.s).buffer), n = cols.length, W = new Float32Array(rows * n);
        for (let r = 0; r < rows; r++) {
          const s = sc[r], off = r * colsFull, o2 = r * n;
          for (let c = 0; c < n; c++) W[o2 + c] = q[off + cols[c]] * s;
        }
        return W;
      };
      const f32 = (b, n) => new Float32Array(b64bytes(b).buffer).slice(0, n);
      const IN = K * S.D + S.DC;
      N.nets[name] = {
        full: !!full, K, D: S.D, DC: S.DC, H1: S.H1, H2: S.H2, IN,
        params: N.V * S.D + LM.conds.length * S.DC + IN * S.H1 + S.H1 + S.H1 * S.H2 + S.H2 + S.H2 * S.D + S.D + N.V,
        E: deq(LM.w.E, N.V, F.D, seq(S.D)), Ec: deq(LM.w.Ec, LM.conds.length, F.DC, seq(S.DC)),
        W1: deq(LM.w.W1, S.H1, K * F.D + F.DC, cols1), W2: deq(LM.w.W2, S.H2, F.H1, seq(S.H1)), Wp: deq(LM.w.Wp, S.D, F.H2, seq(S.H2)),
        b1: f32(LM.w.b1, S.H1), b2: f32(LM.w.b2, S.H2), bp: f32(LM.w.bp, S.D),
      };
    }
    return N.nets[name];
  }

  // 在 CPU 上跑一个网络。begin(条件)：一句话开头调用一次；step(前 K 个词) → 投影后的向量（和每个词的词向量相乘就是这个词的分数）
  function lmCpu(M) {
    const { K, D, DC, H1, H2, IN } = M;
    const cv = new Float32Array(DC), base = new Float32Array(H1), h1 = new Float32Array(H1), h2 = new Float32Array(H2), pr = new Float32Array(D);
    return {
      M,
      begin(cs) { // 条件对整句都一样：先算好它在第一层的贡献
        cv.fill(0);
        for (const c of cs) for (let j = 0; j < DC; j++) cv[j] += M.Ec[c * DC + j];
        for (let j = 0; j < H1; j++) {
          let a = M.b1[j];
          const off = j * IN + K * D;
          for (let i = 0; i < DC; i++) a += M.W1[off + i] * cv[i];
          base[j] = a;
        }
      },
      step(ctx) {
        for (let j = 0; j < H1; j++) {
          let a = base[j];
          const off = j * IN;
          for (let k = 0; k < K; k++) {
            const e = ctx[k] * D, o2 = off + k * D;
            for (let d = 0; d < D; d++) a += M.W1[o2 + d] * M.E[e + d];
          }
          h1[j] = Math.tanh(a);
        }
        for (let j = 0; j < H2; j++) {
          let a = M.b2[j];
          const off = j * H1;
          for (let i = 0; i < H1; i++) a += M.W2[off + i] * h1[i];
          h2[j] = Math.tanh(a);
        }
        for (let d = 0; d < D; d++) {
          let a = M.bp[d];
          const off = d * H2;
          for (let i = 0; i < H2; i++) a += M.Wp[off + i] * h2[i];
          pr[d] = a;
        }
        return pr;
      },
    };
  }

  // 在显卡上跑完整的网络（WebGPU）。三层都是“矩阵 × 向量（+ tanh）”，用同一段着色器，每一行一个线程；
  // 每生成一个词：把输入向量传上去，三层连着算完，把结果（D 个数）读回来。
  const LM_WGSL = `
    struct Dim { rows: u32, cols: u32, act: u32, pad: u32 };
    @group(0) @binding(0) var<uniform> dim: Dim;
    @group(0) @binding(1) var<storage, read> W: array<f32>;
    @group(0) @binding(2) var<storage, read> bias: array<f32>;
    @group(0) @binding(3) var<storage, read> x: array<f32>;
    @group(0) @binding(4) var<storage, read_write> y: array<f32>;
    @compute @workgroup_size(64)
    fn main(@builtin(global_invocation_id) id: vec3<u32>) {
      let r = id.x;
      if (r >= dim.rows) { return; }
      var s = bias[r];
      let o = r * dim.cols;
      for (var j = 0u; j < dim.cols; j = j + 1u) { s = s + W[o + j] * x[j]; }
      if (dim.act == 1u) { s = tanh(s); }
      y[r] = s;
    }`;
  const LM_GPU_LOST = 'LM_GPU_LOST';
  const LM_CPU_FULL = typeof process !== 'undefined' && !!process.env && process.env.LM_FULL === '1'; // 离线工具里：在 CPU 上跑完整的网络（检查用）
  let LMGPU = null, lmGpuState = 'none'; // none | ready | failed
  var LMCPU = null;

  async function lmGpuInit() {
    if (LMGPU || lmGpuState !== 'none') return LMGPU;
    lmGpuState = 'failed';
    try {
      const gpu = typeof navigator !== 'undefined' && navigator.gpu;
      if (!gpu || !LM || !LM.S) return null; // 没有 WebGPU：用小网络
      const adapter = await gpu.requestAdapter();
      if (!adapter) return null;
      const device = await adapter.requestDevice();
      const M = lmModel(true), { K, D, DC, H1, H2, IN } = M, U = GPUBufferUsage;
      const store = (arr) => { const b = device.createBuffer({ size: arr.byteLength, usage: U.STORAGE | U.COPY_DST }); device.queue.writeBuffer(b, 0, arr); return b; };
      const blank = (n, extra) => device.createBuffer({ size: n * 4, usage: U.STORAGE | extra });
      const x = blank(IN, U.COPY_DST), a1 = blank(H1, 0), a2 = blank(H2, 0), out = blank(D, U.COPY_SRC);
      const read = device.createBuffer({ size: D * 4, usage: U.MAP_READ | U.COPY_DST });
      device.pushErrorScope('validation');
      const pipeline = await device.createComputePipelineAsync({ layout: 'auto', compute: { module: device.createShaderModule({ code: LM_WGSL }), entryPoint: 'main' } });
      const layer = (W, b, rows, cols, act, src, dst) => {
        const u = device.createBuffer({ size: 16, usage: U.UNIFORM | U.COPY_DST });
        device.queue.writeBuffer(u, 0, new Uint32Array([rows, cols, act, 0]));
        return { n: Math.ceil(rows / 64), bind: device.createBindGroup({ layout: pipeline.getBindGroupLayout(0), entries: [u, store(W), store(b), src, dst].map((buffer, binding) => ({ binding, resource: { buffer } })) }) };
      };
      const layers = [layer(M.W1, M.b1, H1, IN, 1, x, a1), layer(M.W2, M.b2, H2, H1, 1, a1, a2), layer(M.Wp, M.bp, D, H2, 0, a2, out)];
      if (await device.popErrorScope()) return null;
      const xv = new Float32Array(IN);
      let dead = false;
      const G = {
        M,
        begin(cs) {
          xv.fill(0, K * D);
          for (const c of cs) for (let j = 0; j < DC; j++) xv[K * D + j] += M.Ec[c * DC + j];
        },
        async step(ctx) {
          try {
            if (dead) throw new Error(LM_GPU_LOST);
            for (let k = 0; k < K; k++) xv.set(M.E.subarray(ctx[k] * D, ctx[k] * D + D), k * D);
            device.queue.writeBuffer(x, 0, xv);
            const enc = device.createCommandEncoder();
            for (const l of layers) {
              const p = enc.beginComputePass();
              p.setPipeline(pipeline);
              p.setBindGroup(0, l.bind);
              p.dispatchWorkgroups(l.n);
              p.end();
            }
            enc.copyBufferToBuffer(out, 0, read, 0, D * 4);
            device.queue.submit([enc.finish()]);
            await read.mapAsync(GPUMapMode.READ);
            const pr = new Float32Array(read.getMappedRange().slice(0));
            read.unmap();
            return pr;
          } catch (e) { // 显卡用不了了：之后都用小网络；正在生成的这段讲解由调用方重来
            if (LMGPU === G) LMGPU = null;
            throw new Error(LM_GPU_LOST);
          }
        },
      };
      device.lost.then(() => { dead = true; if (LMGPU === G) LMGPU = null; });
      LMGPU = G;
      lmGpuState = 'ready';
    } catch (e) { LMGPU = null; }
    return LMGPU;
  }

  // 现在用哪个网络：显卡上的完整网络，否则 CPU 上的小网络
  function lmEngine() {
    if (LMGPU) return LMGPU;
    if (!LMCPU) LMCPU = lmCpu(lmModel(LM_CPU_FULL));
    return LMCPU;
  }
  const lmInfo = () => { const e = lmEngine(); return { gpu: e === LMGPU, params: e.M.params, full: e.M.full }; };

  // 自检：同一个输入，显卡算的和 CPU 算的（都是完整的网络）差多少、显卡每个词要多久
  async function lmProbe() {
    const N = lmNet(), G = await lmGpuInit();
    if (!G) return { gpu: false, slim: lmModel(false).params };
    const C = lmCpu(G.M), cs = [0, 1, 2], ctx = new Array(N.K).fill(N.id.get('<bos>'));
    C.begin(cs); G.begin(cs);
    const a = C.step(ctx), t0 = performance.now();
    let b = null;
    for (let i = 0; i < 20; i++) b = await G.step(ctx);
    let diff = 0, mag = 0;
    for (let i = 0; i < a.length; i++) { diff = Math.max(diff, Math.abs(a[i] - b[i])); mag = Math.max(mag, Math.abs(a[i])); }
    return { gpu: true, diff, mag, ms: (performance.now() - t0) / 20, full: G.M.params, slim: lmModel(false).params };
  }

  // 同一句里有一段话说了两遍（连着 3 个词重复出现）就不要
  function lmRepeats(ids) {
    const seen = new Set();
    for (let i = 0; i + 3 <= ids.length; i++) {
      const k = ids.slice(i, i + 3).join(',');
      if (seen.has(k)) return true;
      seen.add(k);
    }
    return false;
  }

  // 把词拼回句子：标点、's、连字符（half-open）、占位词后面的复数 s（⟨cap⟩s → knights）都紧贴前一个词
  function lmDetok(toks) {
    let out = '';
    toks.forEach((t, i) => {
      const glue = i === 0 || /^[.,;:!?)]$/.test(t) || t.startsWith("'") || out.endsWith('(') || t === '-' || out.endsWith('-') || (t === 's' && out.endsWith('⟩'));
      out += (glue ? '' : ' ') + t;
    });
    return out;
  }

  // 生成一句话，返回 { text, v: 用的是第几组说法 }；生成不出合格的就返回 null（调用方退回措辞库）
  // onPart：每生成一个词就把这句话目前的样子报出去（一边生成一边显示用）
  // seen(第几组)：这组说法最近用过几次——优先用最近没用过的
  // 异步：网络在显卡上跑时，每个词都要等显卡把结果送回来
  async function lmGenerate(key, kind, params, rng, reject, onPart, seen) {
    const N = lmNet(), m = LM && LM.meta[key];
    if (!N || !m) return null;
    const ck = N.cid.get('key:' + key), cd = N.cid.get('kind:' + kind);
    if (ck == null || cd == null) return null;
    const have = (slot) => params[slot.slice(1, -1)] != null && params[slot.slice(1, -1)] !== '';
    if (m.req.some((sl) => !have(sl))) return null;
    // 同一个意思的说法分成了若干组，网络被告知“这句用第几组”。能用的组：组里至少有一种句式，它要提到的内容手头都有
    const vars = [];
    m.vars.forEach((alts, b) => {
      if (N.cid.has('var:' + b) && alts.split('|').some((a) => a.split(' ').filter(Boolean).every(have))) vars.push({ b, n: seen ? seen(b) : 0, r: rng() });
    });
    if (!vars.length) return null;
    vars.sort((x, y) => x.n - y.n || x.r - y.r); // 最近没用过的排前面，其余随机
    const eng = lmEngine(), E = eng.M.E, D = eng.M.D, { K, V } = N;
    const BOS = N.id.get('<bos>'), EOS = N.id.get('<eos>'), PAD = N.id.get('<pad>');
    const allow = new Map(Object.entries(m.allow).filter(([sl]) => have(sl)).map(([sl, n]) => [N.id.get(sl), n]));
    const req = m.req.map((sl) => N.id.get(sl));
    const maxLen = 40;
    const logit = new Float32Array(V);
    const textOf = (ids) => lmDetok(ids.map((i) => LM.vocab[i])).replace(/⟨([A-Za-z0-9]+)⟩/g, (m0, name) => String(params[name]));
    const guard = lmGuard(key), ALL = guard ? null : Int32Array.from({ length: V }, (_, v) => v);
    const isSlot = new Uint8Array(V);
    N.slots.forEach((sid) => (isSlot[sid] = 1));
    for (let attempt = 0; attempt < LM_TRIES; attempt++) {
      // 这一遍用第几组说法。条件（意思、评级、组号）对整句都一样
      const va = vars[attempt % vars.length];
      eng.begin([ck, cd, N.cid.get('var:' + va.b)]);
      const ctx = new Array(K).fill(BOS), out = [], used = new Map();
      let done = false;
      for (let step = 0; step < maxLen && !done; step++) {
        // 候选词：语料里能接在前两个词后面的词（没有语料时就是整个词表）
        const cand = guard ? guard.get(lmCtxKey(ctx, LM_CTX, V)) : ALL;
        if (!cand) break;
        const pr = await eng.step(ctx);
        // 约束：不用特殊词；用不到的占位词不许出现、每个最多用到语料里出现过的次数；必须提到的没写全不许结束；不许连着三次同一个词
        const reqLeft = req.some((sid) => !used.has(sid)), rep2 = out.length >= 2 && out[out.length - 1] === out[out.length - 2] ? out[out.length - 1] : -1;
        const top = [];
        for (const v of cand) {
          if (v === PAD || v === BOS || v === rep2 || (v === EOS && reqLeft)) continue;
          if (isSlot[v] && (!allow.has(v) || (used.get(v) || 0) >= allow.get(v))) continue;
          let a = N.bo[v];
          const off = v * D;
          for (let d = 0; d < D; d++) a += E[off + d] * pr[d];
          logit[v] = a;
          // 按温度抽样，只从分数最高的几个里挑
          if (top.length < LM_TOPK) { top.push(v); top.sort((x, y) => logit[y] - logit[x]); }
          else if (a > logit[top[LM_TOPK - 1]]) { top[LM_TOPK - 1] = v; top.sort((x, y) => logit[y] - logit[x]); }
        }
        if (!top.length) break;
        const mx = logit[top[0]], w = top.map((v) => Math.exp((logit[v] - mx) / LM_TEMP)).filter((x) => x >= LM_MINP), z = w.reduce((a, b) => a + b, 0);
        let r = rng() * z, k = 0;
        while (k < w.length - 1 && (r -= w[k]) > 0) k++;
        const tok = top[k];
        if (tok === EOS) { done = true; break; }
        out.push(tok);
        if (onPart) onPart(textOf(out));
        if (allow.has(tok)) used.set(tok, (used.get(tok) || 0) + 1);
        ctx.shift();
        ctx.push(tok);
      }
      if (!done || !out.length || lmRepeats(out)) continue;
      const text = textOf(out);
      if (reject && reject(text)) continue;
      return { text, v: va.b };
    }
    return null;
  }

  // recent / recentTexts：最近几步用过的候选和句子，网络会避开重复
  // known：这次打开页面后已经解释过的术语（不再重复解释）
  function makeSelector(c, seedStr, recent, recentTexts, known) {
    const pre = nnPre(ctxVec(c)), rng = mulberry32(hash(seedStr)), used = [], texts = [], toolLog = [];
    const cnt = (id) => recent.reduce((n, r) => n + (r === id ? 1 : 0), 0);
    function choose(feats, ids) {
      const sc = feats.map((f) => nnScore(pre, f));
      const pr = softmax(sc, NN_T);
      let r = rng(), k = 0;
      while (k < pr.length - 1 && (r -= pr[k]) > 0) k++;
      used.push(ids[k]);
      return k;
    }
    const render1 = (x, p) => (typeof x === 'function' ? x(p || {}) : x);
    const words = (t) => t.replace(/\{([^{}]+)\}/g, (m, alts) => {
      const o = alts.split('|');
      return o[choose(o.map((w) => candFeat('word', null, w, cnt('w:' + w), 0, 0)), o.map((w) => 'w:' + w))];
    });
    return {
      used, texts,
      known: new Set(known || []), learned: [],                    // 已经解释过的术语 / 这段讲解里新解释的
      toolLog, tool: (name, args) => callTool(name, args, toolLog), // 查知识库（调用记录留在 toolLog 里）
      // 先让语言模型一个词一个词地生成；生成不出合格的句子（或和最近说过的太像），才从措辞库里挑
      async gen(key, p, onPart) {
        const ctxTexts = recentTexts.concat(texts);
        const g = await lmGenerate(key, c.kind, p || {}, rng, (t) => simTo(ctxTexts, t) > 0.85, onPart, (b) => cnt(`lm:${key}#${b}`));
        if (!g) return null;
        texts.push(g.text);
        used.push(`lm:${key}#${g.v}`); // 记下用了第几组说法：之后几步优先换别的组
        return g.text;
      },
      async pick(key, pool, p, onPart) {
        const g = await this.gen(key, p, onPart);
        if (g) return g;
        const raw = pool.map((x) => render1(x, p));
        const ids = raw.map((_, i) => key + '#' + i);
        const cat = catOf(key), ctxTexts = recentTexts.concat(texts);
        const k = raw.length < 2 ? 0
          : choose(raw.map((t, i) => candFeat(cat, null, stripSlots(t), cnt(ids[i]), simTo(ctxTexts, stripSlots(t)), 0)), ids);
        const t = words(raw[k]);
        texts.push(t);
        return t;
      },
      include(slot) {
        const ids = ['inc:' + slot + ':0', 'inc:' + slot + ':1'];
        return choose([0, 1].map((v) => candFeat('include', slot, '', v ? cnt(ids[1]) : 0, 0, v)), ids) === 1;
      },
      // 从候选理由里一条条挑，第一条之后多一个“到此为止”选项；subj：0 = 这步棋，1 = 推荐着法
      select(rs, max, subj, W) {
        const left = rs.slice(), chosen = [], ctxTexts = recentTexts.concat(texts);
        const textOf = (r) => stripSlots(r.text || render1(W[r.key][0], r.p));
        while (left.length && chosen.length < max) {
          const order = chosen.length;
          const feats = left.map((r) => candFeat('reason', null, textOf(r), cnt('r:' + r.type), simTo(ctxTexts, textOf(r)), 0,
            { type: r.type, mag: r.mag, mate: r.mate, subj, order }));
          const ids = left.map((r) => 'r:' + r.type);
          if (order > 0) {
            feats.push(candFeat('reason', null, '', 0, 0, 0, { type: 'stop', mag: 0, mate: 0, subj, order }));
            ids.push('r:stop');
          }
          const k = choose(feats, ids);
          if (k >= left.length) break;
          chosen.push(left.splice(k, 1)[0]);
        }
        return chosen;
      },
    };
  }

  // ---------- 界面文字 ----------
  const TXT = {
    W: W_EN,
    title: '♟ Chess.com Coach', collapse: 'Collapse',
    side: { auto: 'Auto', w: 'White', b: 'Black' }, sideTip: 'Which side to comment on: Auto (board orientation) → White → Black',
    waiting: 'Waiting for position…', analysing: 'Querying…',
    fetching: 'Querying online engine…', lichess: 'Lichess cloud database', chessApi: 'chess-api.com online Stockfish',
    local: 'Local Stockfish 10 (fallback)', localRunning: 'Online engines slow or unreachable, computing locally…',
    depth: (d) => ` · depth ${d}`,
    white: 'White', black: 'Black', even: 'Equal position',
    slight: (s) => `${s} is slightly better`, clear: (s) => `${s} has a clear advantage`, winning: (s) => `${s} is winning`,
    mateIn: (s, n) => `${s} mates in ${n}`, matedWin: (s) => `${s} wins by checkmate`, stalemate: 'Stalemate',
    allFail: 'Neither online nor local engine is available',
    change: (a, b) => `Your win chance ${a} → ${b}`,
    promptT: 'Coach', prompt: "Your move. Play it and I'll walk you through it!",
    modelT: 'Coach model', modelLoading: 'Downloading the coach model (only needed once per version)…', modelFail: 'Could not download the coach model from GitHub. Retrying in 30 seconds.',
    thinkingT: 'Thinking…', thinking: 'The engine is evaluating your move',
    noEvalT: 'No comment', noEval: 'No evaluation for this position',
    oppMoved: (m) => `Opponent played ${m}. Your move.`,
    ttsTip: 'Read comments aloud automatically: on / off', read: 'Read this comment aloud', stop: 'Stop reading',
    voiceTip: 'Voice used for reading. The most human-like are Microsoft "Natural" voices (free in the Edge browser), then Google online voices (Chrome).',
    noVoice: 'No English voice in this browser',
    dupWarn: 'Another copy of this script is also running (e.g. the old "Chess.com 复盘胜率面板"), which causes double reading and mismatched text. Please delete or disable the old one in Tampermonkey.',
    edgeHint: 'For the most human-like voice, open this page in Microsoft Edge: it uses Microsoft "Natural" voices such as Ava, for free.',
    four: {
      title: 'Four-player chess · Teams', teams: ['Red-Yellow', 'Blue-Green'], teamsShort: ['R-Y', 'B-G'],
      ffa: 'Free-for-all (FFA) is not supported yet; only Teams games are.', ffaShort: 'FFA not supported',
      turnUnknown: 'Analysis starts after the next move', thinking: 'Four-player engine thinking…', noEval: 'No evaluation for this position', gameOver: 'Game over',
      engine: 'Titan four-player engine (runs locally)', engineLoading: 'Loading four-player engine…', engineFail: 'Four-player engine failed to load',
      even: 'Teams are level', lead: (t) => `${t} ahead`, behind: (t) => `${t} behind`, moved: (who, m) => `${who} played ${m}`,
    },
    menu: {
      open: 'Menu', close: 'Close menu',
      nav: { overview: 'Overview', mistakes: 'Mistakes', settings: 'Settings' },
      overviewT: 'Last 30 days', total: 'wrong moves', blunders: 'blunders', mistakes: 'mistakes', inaccs: 'inaccuracies',
      weakT: 'What goes wrong most', noData: 'Nothing recorded yet. Review a game on this page and your wrong moves are collected here.',
      why: {
        hanging: 'Left a piece unprotected', ignored: "Missed the opponent's threat", tactic: 'Walked into a tactic',
        mate: 'Allowed a mating attack', missedMate: 'Missed a checkmate', other: 'A stronger move was available',
      },
      focus: {
        hanging: 'Focus: before every move, check that the square you move to is safe and that nothing is left unprotected.',
        ignored: "Focus: before every move, ask what the opponent's last move is threatening.",
        tactic: 'Focus: look at every check and capture your opponent has before you move.',
        mate: 'Focus: keep an eye on your own king, and count the attackers around it.',
        missedMate: 'Focus: when the enemy king is exposed, look at every check first.',
        other: 'Focus: compare two or three candidate moves before you play one.',
      },
      statusT: 'Status', engine: 'Engine', localEngine: 'Local engine', sf: { idle: 'not loaded', loading: 'loading…', ready: 'ready', failed: 'failed to load' },
      voice: 'Voice', version: 'Version', model: 'Model version', lm: 'Language model', lmGpu: (n) => `${n}M parameters, on the GPU (WebGPU)`, lmCpu: (n) => `${n}M parameters, on the CPU (no WebGPU)`,
      mistakesT: (n) => `${n} wrong move${n === 1 ? '' : 's'} in the last 30 days`, today: 'Today', yesterday: 'Yesterday',
      openPos: 'Open this position', remove: 'Remove', copy: 'Copy all', copied: 'Copied ✓', copyTip: 'Copy the whole mistake book as text, to paste into a chat and go through it',
      settingsT: 'Settings', gRead: 'Reading', gMarks: 'Board marks', gBook: 'Mistake book',
      sTts: 'Read comments aloud', sVoice: 'Voice', sSide: 'Comment on', sRate: 'Reading speed', sRateD: 'Type a number from 0.5 to 3 (1 is normal speed)',
      sMarks: 'Mark the board', sMarksD: 'Arrows and circles on the board. Orange: your wrong move. Red: how your opponent punishes it. Green: what you should have played. Yellow: what your move does. Blue: a threat you stopped.',
      sAnim: 'Animated drawing', sAnimD: 'A pointer draws the marks one by one',
      sThreats: "Opponent's threats", sThreatsD: 'On your turn, mark what the opponent is threatening',
      sBetter: 'Better move', sBetterD: 'After a wrong move, mark the move you should have played',
      sInacc: 'Record inaccuracies', sInaccD: 'Keep small slips in the mistake book too',
      clear: 'Clear mistake book', clearSure: 'Click again to clear',
    },
    labels: {
      mate: '👑 Checkmate', mating: '♛ Mate ahead', missedMate: '?? Missed mate', best: '★ Best move', excellent: '✓ Excellent',
      good: '👍 Good', inaccuracy: '?! Inaccuracy', mistake: '? Mistake', blunder: '?? Blunder',
    },
  };
  let sideMode = GM_getValue('cwp_side', 'auto');
  // 设置（菜单里的 Settings 页）：没存过的项用默认值
  const opts = { ttsRate: 1.35, marks: true, markAnimate: true, markThreats: true, markBetter: true, bookInacc: true, ...GM_getValue('cwp_opts', {}) };
  const setOpt = (k, v) => { opts[k] = v; GM_setValue('cwp_opts', opts); };
  const L = () => TXT;

  // ---------- 样式 & 面板 ----------
  const css = `
  #cwp{position:fixed;z-index:99999;width:330px;background:#262421;color:#e8e6e3;border-radius:10px;
       box-shadow:0 8px 24px rgba(0,0,0,.45);font:13px/1.5 -apple-system,"PingFang SC",sans-serif;user-select:none}
  #cwp .hd{display:flex;justify-content:space-between;align-items:center;padding:8px 12px;background:#1d1b19;
       border-radius:10px 10px 0 0;cursor:move;font-weight:600}
  #cwp .hd .btns{display:flex;gap:6px;align-items:center}
  #cwp .hd button{background:none;border:0;color:#aaa;font-size:16px;cursor:pointer;line-height:1}
  #cwp .hd button.chip{font-size:11px;font-weight:700;border:1px solid #555;border-radius:4px;padding:2px 6px}
  #cwp .hd button:hover{color:#fff}
  #cwp .bd{padding:12px}
  #cwp.min .bd,#cwp.min .mn{display:none}
  #cwp .ev{font-size:34px;font-weight:700;text-align:center;letter-spacing:.5px}
  #cwp .sub{text-align:center;color:#9e9b98;font-size:12px;margin-bottom:10px}
  #cwp .bar{position:relative;height:22px;background:#403d39;border-radius:6px;overflow:hidden}
  #cwp .bar .w{position:absolute;left:0;top:0;bottom:0;background:#f0f0f0;transition:width .35s ease}
  #cwp .bar span{position:absolute;top:2px;font-size:12px;font-weight:700}
  #cwp .bar .lw{left:8px;color:#222}
  #cwp .bar .lb{right:8px;color:#eee}
  #cwp .cm{margin-top:12px;padding:10px;background:#1d1b19;border-radius:8px;border-left:4px solid #666;min-height:40px;user-select:text}
  #cwp .nt{font-size:11px;color:#8a8784;font-style:italic;margin-bottom:6px}
  #cwp .nt:empty{display:none}
  #cwp .ct{font-weight:700;margin-bottom:6px;font-size:14px}
  #cwp .cx{color:#d4d1ce;font-size:12.5px;max-height:320px;overflow-y:auto;padding-right:2px}
  #cwp .cx p{margin:0 0 8px}
  #cwp .cx p:last-child{margin-bottom:0}
  #cwp .cn{margin-top:8px;font-size:11px;color:#8a8784}
  #cwp .cn:empty{display:none}
  #cwp .st,#cwp .ast{margin-top:4px;font-size:11px;color:#777;text-align:right}
  #cwp .st{margin-top:8px}
  #cwp .ast:empty{display:none}
  #cwp .fb{display:flex;align-items:center;gap:4px;margin-top:8px}
  #cwp .fb:empty{display:none}
  #cwp .fb button{background:#312e2b;border:1px solid #4a4744;border-radius:5px;padding:2px 7px;cursor:pointer;font-size:13px;line-height:1.3}
  #cwp .fb button:hover:not(:disabled){border-color:#81b64c}
  #cwp .fb button:disabled{opacity:.35;cursor:default}
  #cwp .vhint{margin-top:6px;font-size:11px;color:#8a8784;line-height:1.4}
  #cwp .fb select{flex:1;min-width:0;background:#312e2b;color:#c9c6c3;border:1px solid #4a4744;border-radius:5px;font-size:11px;padding:2px 4px}
  #cwp.anim{transition:width .3s ease,left .3s ease}
  #cwp.menu{width:660px}
  #cwp .mn{display:none}
  #cwp.menu .bd{display:none}
  #cwp.menu .mn{display:flex;height:440px;animation:cwpIn .32s ease}
  @keyframes cwpIn{from{opacity:0;transform:translateX(16px)}to{opacity:1;transform:none}}
  #cwp .nav{width:128px;flex:none;background:#211f1c;padding:8px 6px;border-radius:0 0 0 10px;display:flex;flex-direction:column;gap:2px}
  #cwp .nav button{display:flex;align-items:center;gap:8px;background:none;border:0;color:#b5b2ae;font:inherit;text-align:left;padding:7px 9px;border-radius:6px;cursor:pointer}
  #cwp .nav button:hover{background:#2b2926;color:#fff}
  #cwp .nav button.on{background:#3a3734;color:#fff;font-weight:600}
  #cwp .pg{flex:1;min-width:0;padding:10px 14px 14px;overflow-y:auto;user-select:text}
  #cwp .pg h3{margin:2px 0 10px;font-size:15px;display:flex;justify-content:space-between;align-items:center}
  #cwp .copy{background:#312e2b;border:1px solid #4a4744;color:#c9c6c3;border-radius:6px;padding:3px 9px;cursor:pointer;font:inherit;font-size:12px;font-weight:400}
  #cwp .copy:hover{border-color:#81b64c;color:#fff}
  #cwp .pg h4{margin:14px 0 6px;font-size:11px;letter-spacing:.6px;text-transform:uppercase;color:#8a8784}
  #cwp .dim{color:#8a8784;font-size:12px}
  #cwp .cards{display:grid;grid-template-columns:repeat(4,1fr);gap:8px}
  #cwp .card{background:#1d1b19;border-radius:8px;padding:8px 6px;text-align:center}
  #cwp .card b{display:block;font-size:22px;line-height:1.2}
  #cwp .card span{font-size:11px;color:#9e9b98}
  #cwp .wk{display:grid;grid-template-columns:190px 1fr 24px;align-items:center;gap:8px;font-size:12px;margin:5px 0}
  #cwp .wk i{height:8px;background:#403d39;border-radius:4px;overflow:hidden}
  #cwp .wk u{display:block;height:100%;background:#fa412d;border-radius:4px}
  #cwp .wk b{text-align:right}
  #cwp .tipbox{margin-top:10px;padding:8px 10px;background:#1d1b19;border-left:3px solid #81b64c;border-radius:6px;font-size:12px}
  #cwp .kv{display:grid;grid-template-columns:110px 1fr;gap:4px 8px;font-size:12px}
  #cwp .kv span{color:#9e9b98}
  #cwp .kv b{font-weight:500}
  #cwp .dayh{margin:12px 0 4px;font-size:11px;color:#8a8784;text-transform:uppercase;letter-spacing:.6px}
  #cwp .mk{background:#1d1b19;border-radius:8px;margin-bottom:5px}
  #cwp .mkh{display:flex;align-items:center;gap:8px;padding:7px 10px;cursor:pointer;user-select:none;border-radius:8px}
  #cwp .mkh:hover{background:#2b2926}
  #cwp .tag{flex:none;min-width:22px;text-align:center;border-radius:4px;padding:0 5px;color:#fff;font-weight:700;font-size:12px}
  #cwp .mv{flex:1;font-weight:600}
  #cwp .dr{color:#9e9b98;font-size:12px}
  #cwp .ar{color:#777}
  #cwp .mkb{display:flex;gap:12px;padding:4px 10px 10px}
  #cwp .mkt{min-width:0;font-size:12px;color:#d4d1ce}
  #cwp .mkt p{margin:4px 0 8px}
  #cwp .mkt .why{font-weight:700;color:#e8e6e3}
  #cwp .lnk{display:flex;gap:14px}
  #cwp .lnk a{color:#81b64c;text-decoration:none}
  #cwp .lnk a:hover{text-decoration:underline}
  #cwp .mb{position:relative;flex:none;display:grid;grid-template-columns:repeat(8,1fr);width:176px;height:176px;border-radius:4px;overflow:hidden}
  #cwp .mb i{display:flex;align-items:center;justify-content:center;font-style:normal;font-size:17px;line-height:1}
  #cwp .mb i.l{background:#ebecd0}
  #cwp .mb i.d{background:#739552}
  #cwp .mb b{font-weight:400}
  #cwp .mb b.w{color:#fff;text-shadow:0 0 1px #000,0 0 1px #000,0 1px 1px #000}
  #cwp .mb b.b{color:#111}
  #cwp .mb svg{position:absolute;left:0;top:0;width:100%;height:100%;pointer-events:none}
  #cwp .opt{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:6px 0;cursor:pointer}
  #cwp .opt.off{opacity:.45}
  #cwp .opt b{display:block;font-weight:500}
  #cwp .opt small{display:block;color:#8a8784;font-size:11px;line-height:1.35}
  #cwp .opt select{max-width:220px;background:#312e2b;color:#c9c6c3;border:1px solid #4a4744;border-radius:5px;font-size:12px;padding:3px 4px}
  #cwp .opt input.num{width:56px;text-align:center;background:#312e2b;color:#e8e6e3;border:1px solid #4a4744;border-radius:5px;font:inherit;font-size:12px;padding:3px 5px}
  #cwp .sw{position:relative;flex:none;width:34px;height:20px}
  #cwp .sw input{position:absolute;opacity:0;width:100%;height:100%;margin:0;cursor:pointer}
  #cwp .sw i{position:absolute;left:0;top:0;right:0;bottom:0;background:#4a4744;border-radius:10px;transition:background .15s;pointer-events:none}
  #cwp .sw i:after{content:"";position:absolute;left:2px;top:2px;width:16px;height:16px;background:#fff;border-radius:50%;transition:transform .15s}
  #cwp .sw input:checked+i{background:#81b64c}
  #cwp .sw input:checked+i:after{transform:translateX(14px)}
  #cwp .danger{margin-top:8px;background:#312e2b;border:1px solid #6b3a34;color:#f08a7d;border-radius:6px;padding:5px 10px;cursor:pointer;font:inherit}
  #cwp .danger:hover{border-color:#fa412d}`;
  const style = document.createElement('style');
  style.textContent = css;
  document.head.appendChild(style);

  const panel = document.createElement('div');
  panel.id = 'cwp';
  panel.innerHTML = `
    <div class="hd"><span class="ttl"></span>
      <div class="btns"><button class="chip tts"></button><button class="chip side"></button><button class="menu-btn">☰</button><button class="min-btn">–</button></div>
    </div>
    <div class="mn"><div class="nav"></div><div class="pg"></div></div>
    <div class="bd">
      <div class="ev">0.0</div>
      <div class="sub"></div>
      <div class="bar"><div class="w" style="width:50%"></div><span class="lw">50%</span><span class="lb">50%</span></div>
      <div class="cm"><div class="nt"></div><div class="ct"></div><div class="cx"></div><div class="cn"></div><div class="fb"></div></div>
      <div class="st"></div>
    </div>`;
  document.body.appendChild(panel);
  const $ = (s) => panel.querySelector(s);

  // 位置记忆 + 拖动
  const pos = GM_getValue('cwp_pos', { left: window.innerWidth - 360, top: 100 });
  function place(l, t) {
    l = Math.max(0, Math.min(window.innerWidth - panel.offsetWidth, l));
    t = Math.max(0, Math.min(window.innerHeight - 40, t));
    panel.style.left = l + 'px';
    panel.style.top = t + 'px';
  }
  place(pos.left, pos.top);
  if (GM_getValue('cwp_min', false)) panel.classList.add('min');

  const hd = $('.hd');
  hd.addEventListener('pointerdown', (e) => {
    if (e.target.tagName === 'BUTTON') return;
    const r = panel.getBoundingClientRect();
    const dx = e.clientX - r.left, dy = e.clientY - r.top;
    hd.setPointerCapture(e.pointerId);
    const move = (ev) => place(ev.clientX - dx, ev.clientY - dy);
    const up = () => {
      hd.removeEventListener('pointermove', move);
      hd.removeEventListener('pointerup', up);
      GM_setValue('cwp_pos', { left: parseInt(panel.style.left), top: parseInt(panel.style.top) });
    };
    hd.addEventListener('pointermove', move);
    hd.addEventListener('pointerup', up);
  });
  $('.menu-btn').addEventListener('click', () => toggleMenu(!menuOpen));
  $('.min-btn').addEventListener('click', () => {
    if (menuOpen) { toggleMenu(false); return; } // 菜单开着：先收起菜单
    panel.classList.toggle('min');
    GM_setValue('cwp_min', panel.classList.contains('min'));
  });
  $('.tts').addEventListener('click', () => {
    ttsAuto = !ttsAuto;
    GM_setValue('cwp_tts', ttsAuto);
    if (!ttsAuto) stopSpeak();
    render();
  });
  $('.side').addEventListener('click', () => {
    sideMode = { auto: 'w', w: 'b', b: 'auto' }[sideMode];
    GM_setValue('cwp_side', sideMode);
    render();
  });

  // ---------- 读取棋盘 FEN ----------
  function getBoardEl() {
    return unsafeWindow.document.querySelector('wc-chess-board, chess-board');
  }

  // 己方：手动指定，或者看棋盘是否翻转（黑方在下 = 执黑）
  function mySide() {
    if (sideMode !== 'auto') return sideMode;
    const b = getBoardEl();
    return b && b.classList.contains('flipped') ? 'b' : 'w';
  }

  function domPlacement(board) {
    const g = {};
    board.querySelectorAll('.piece').forEach((el) => {
      const c = [...el.classList];
      const p = c.find((x) => /^[wb][pnbrqk]$/.test(x));
      const s = c.find((x) => /^square-\d\d$/.test(x));
      if (!p || !s) return;
      g[FILES[+s[7] - 1] + s[8]] = p[0] === 'w' ? p[1].toUpperCase() : p[1];
    });
    if (!Object.keys(g).length) return null;
    const rows = [];
    for (let r = 8; r >= 1; r--) {
      let row = '', e = 0;
      for (let f = 0; f < 8; f++) {
        const p = g[FILES[f] + r];
        if (p) { if (e) { row += e; e = 0; } row += p; } else e++;
      }
      if (e) row += e;
      rows.push(row);
    }
    return rows.join('/');
  }

  function castling(b) {
    let s = '';
    if (b.e1 === 'K') { if (b.h1 === 'R') s += 'K'; if (b.a1 === 'R') s += 'Q'; }
    if (b.e8 === 'k') { if (b.h8 === 'r') s += 'k'; if (b.a8 === 'r') s += 'q'; }
    return s || '-';
  }

  let lastDomTurn = 'w';
  function readFen() {
    const board = getBoardEl();
    if (!board) return null;
    try {
      const g = board.game;
      if (g && typeof g.getFEN === 'function') return { fen: g.getFEN(), exact: true };
    } catch (e) { /* 走 DOM 兜底 */ }

    // 兜底：从棋子 DOM 拼 FEN，行棋方靠“上一步是谁动的”推断
    const placement = domPlacement(board);
    if (!placement) return null;
    let turn = lastDomTurn;
    if (placement === START) turn = 'w';
    else if (cur && cur.fen.split(' ')[0] !== placement) {
      const mv = diffMove(cur.fen, placement);
      if (mv) turn = mv.mover === 'w' ? 'b' : 'w';
    } else if (cur) turn = cur.turn;
    lastDomTurn = turn;
    return { fen: `${placement} ${turn} ${castling(parseBoard(placement))} - 0 1`, exact: false };
  }

  // ---------- 引擎：Lichess 云端库 → chess-api.com → 本地 Stockfish ----------
  let cur = null, prev = null, lastMove = null;
  let pairs = {}; // 每一方最近一步：{ prev: 走之前, cur: 走之后, move }
  const evals = new Map(); // fen → 评估结果（缓存，来回翻棋谱不重复请求）
  let lichessDownUntil = 0, apiDownUntil = 0;

  const gmReq = (opts) => new Promise((res, rej) => {
    const ms = opts.timeout || 8000;
    const req = GM_xmlhttpRequest({ ...opts, timeout: ms, onload: res, onerror: rej, ontimeout: rej });
    setTimeout(() => { rej(new Error('timeout')); try { req.abort(); } catch (err) { /* 已经结束了 */ } }, ms + 100); // 自己再掐一次表：接口的超时万一没触发，也不会一直等下去
  });

  // Lichess 的易位写成“王吃车”（e1h1），统一成 e1g1
  function normPv(fen, moves) {
    let b = parseBoard(fen);
    return moves.map((m, i) => {
      if (i > 6 || !m) return m;
      const p = b[m.slice(0, 2)], t = b[m.slice(2, 4)];
      if (p && t && p.toLowerCase() === 'k' && t.toLowerCase() === 'r' && colorOf(p) === colorOf(t)) {
        m = m.slice(0, 2) + (m[2] > m[0] ? 'g' : 'c') + m[1];
      }
      b = applyUci(b, m);
      return m;
    });
  }

  function evalOf(fen) {
    let e = evals.get(fen);
    if (!e) {
      e = { fen, turn: fen.split(' ')[1], cpW: null, mateW: null, depth: 0, best: null, pv: [], done: false, src: null, at: Date.now() };
      evals.set(fen, e);
      fetchLichess(e);
    }
    return e;
  }

  async function fetchLichess(e) {
    if (Date.now() < lichessDownUntil) return fetchChessApi(e);
    try {
      const r = await gmReq({ method: 'GET', url: LICHESS_URL + encodeURIComponent(e.fen), timeout: ONLINE_MS });
      if (r.status === 429 || r.status >= 500) lichessDownUntil = Date.now() + DOWN_MS;
      if (r.status !== 200) return fetchChessApi(e); // 404 = 库里没有这个局面
      const d = JSON.parse(r.responseText), pv = d.pvs[0];
      e.cpW = pv.cp ?? null;
      e.mateW = pv.mate ?? null;
      e.pv = normPv(e.fen, pv.moves.split(' '));
      e.best = e.pv[0];
      e.depth = d.depth;
      e.src = 'lichess';
      e.done = true;
      render();
    } catch (err) {
      lichessDownUntil = Date.now() + DOWN_MS;
      fetchChessApi(e);
    }
  }

  async function fetchChessApi(e) {
    const left = ONLINE_MS - (Date.now() - e.at); // 这个局面在线还能等多久；剩得太少就不问了，直接本地算
    if (Date.now() < apiDownUntil || left < 300) return localEval(e);
    try {
      const r = await gmReq({
        method: 'POST', url: CHESS_API_URL,
        headers: { 'Content-Type': 'application/json' },
        data: JSON.stringify({ fen: e.fen, depth: 18 }),
        timeout: left,
      });
      if (r.status !== 200) throw new Error('HTTP ' + r.status);
      const d = JSON.parse(r.responseText);
      if (d.type === 'error') {
        // 没有合法着法：被将军 = 被将杀，否则 = 逼和
        if (!/move must not be undefined/.test(d.text || '')) throw new Error(d.text);
        e.over = inCheck(e.fen) ? 'mate' : 'draw';
      } else {
        e.mateW = d.mate != null ? +d.mate : null; // chess-api 的分数和杀棋步数都是白方视角
        e.cpW = e.mateW == null ? +d.centipawns : null;
        e.pv = [d.move, ...(d.continuationArr || [])];
        e.best = d.move;
        e.depth = d.depth;
      }
      e.src = 'chessApi';
      e.done = true;
      render();
    } catch (err) {
      apiDownUntil = Date.now() + DOWN_MS;
      localEval(e);
    }
  }

  // ---------- 本地 Stockfish：在线接口连不上、或者超过 ONLINE_MS 还没答复时的兜底 ----------
  // 页面一打开就加载好（见脚本末尾），轮到它时不用再等下载和启动
  let sf = null, sfState = 'idle'; // idle | loading | ready | failed
  let sfJob = null;
  const sfQueue = [];

  function localEval(e) {
    e.src = 'local';
    if (sfState === 'failed') { e.error = 'allFail'; e.done = true; render(); return; }
    if (e === cur) sfQueue.unshift(e); else sfQueue.push(e);
    if (sfState === 'idle') loadStockfish();
    else if (sfState === 'ready') sfNext();
    render();
  }

  async function loadStockfish() {
    sfState = 'loading';
    try {
      // 优先用安装脚本时存下来的副本（断网也能用），没有再去下载
      let code = null;
      try { code = GM_getResourceText('STOCKFISH'); } catch (err) { /* 没有 @resource */ }
      if (!code) {
        const r = await gmReq({ method: 'GET', url: SF_URL, timeout: 30000 });
        if (r.status !== 200) throw new Error('HTTP ' + r.status);
        code = r.responseText;
      }
      sf = new Worker(URL.createObjectURL(new Blob([code], { type: 'application/javascript' })));
      sf.onmessage = (ev) => sfLine(String(ev.data));
      sf.onerror = sfFail;
      sf.postMessage('uci');
      sfState = 'ready';
      sfNext();
    } catch (err) {
      sfFail();
    }
  }

  function sfFail() {
    sfState = 'failed';
    const jobs = sfJob ? [sfJob, ...sfQueue] : [...sfQueue];
    sfJob = null;
    sfQueue.length = 0;
    for (const e of jobs) { e.error = 'allFail'; e.done = true; }
    render();
  }

  function sfNext() {
    if (sfJob || !sfQueue.length) return;
    sfJob = sfQueue.shift();
    sf.postMessage('position fen ' + sfJob.fen);
    sf.postMessage('go depth 18 movetime 3000');
  }

  function sfLine(line) {
    const e = sfJob;
    if (!e) return;
    if (line.startsWith('bestmove')) {
      const m = line.split(' ')[1];
      if (m && m !== '(none)') {
        e.best = m;
        if (!e.pv.length) e.pv = [m];
      } else if (!e.over) e.over = inCheck(e.fen) ? 'mate' : 'draw';
      e.done = true;
      sfJob = null;
      render();
      sfNext();
      return;
    }
    if (!line.startsWith('info') || !line.includes(' score ') || / (lowerbound|upperbound)/.test(line)) return;
    const s = line.match(/ score (cp|mate) (-?\d+)/);
    if (!s) return;
    const sign = e.turn === 'w' ? 1 : -1; // 引擎分数是“行棋方视角”，统一换成白方视角
    if (s[1] === 'mate' && +s[2] === 0) { e.over = 'mate'; return; }
    if (s[1] === 'cp') { e.cpW = sign * +s[2]; e.mateW = null; }
    else { e.mateW = sign * +s[2]; e.cpW = null; }
    e.depth = +(line.match(/ depth (\d+)/) || [0, 0])[1];
    const pv = line.match(/ pv (.+)$/);
    if (pv) {
      e.pv = pv[1].trim().split(/\s+/);
      e.best = e.pv[0];
    }
    if (e === cur) render();
  }

  // ---------- 选词网络：运行时（每步的讲解缓存起来；记住最近用过的说法，避免重复） ----------
  const recentIds = GM_getValue('cwp_nn_recent', []);
  const recentTexts = [];
  const knownTerms = new Set(); // 这次打开页面后已经解释过的术语
  const compCache = new Map();
  let curComp = null;

  function remember(used, texts) {
    recentIds.push(...used);
    recentIds.splice(0, Math.max(0, recentIds.length - 80));
    recentTexts.push(...texts);
    recentTexts.splice(0, Math.max(0, recentTexts.length - 16));
    GM_setValue('cwp_nn_recent', recentIds);
  }

  // ---------- 模型权重：从 GitHub 下载，存在浏览器里 ----------
  // 仓库里的 model/ 文件夹：lm.json（语言模型）、nn.json（选理由的网络）、version.json（各自的版本号）。
  // 每次打开页面先看 version.json：版本和浏览器里存着的一样就直接用存着的，变了才重新下载。连不上 GitHub 时也用存着的。
  const MODEL_URL = 'https://raw.githubusercontent.com/TonyD365/Chess-Coach/main/model/';
  let modelState = 'loading', modelText = null, modelVer = null; // loading | ready | failed
  const modelDb = (mode, fn) => new Promise((res, rej) => {
    const o = indexedDB.open('cwp-coach-model', 1);
    o.onupgradeneeded = () => o.result.createObjectStore('parts');
    o.onerror = () => rej(o.error);
    o.onsuccess = () => {
      const tx = o.result.transaction('parts', mode), r = fn(tx.objectStore('parts'));
      tx.oncomplete = () => { o.result.close(); res(r.result); };
      tx.onerror = () => { o.result.close(); rej(tx.error); };
    };
  });
  async function loadModel() {
    const text = {}, ver = {};
    let remote = null;
    try {
      const r = await gmReq({ method: 'GET', url: MODEL_URL + 'version.json?t=' + Date.now(), timeout: 8000 });
      if (r.status === 200) remote = JSON.parse(r.responseText);
    } catch (e) { /* 连不上：用存着的 */ }
    for (const part of ['lm', 'nn']) {
      let saved = null;
      try { saved = await modelDb('readonly', (st) => st.get(part)); } catch (e) { /* 浏览器不让存：每次都下载 */ }
      if (saved && saved.text && (!remote || remote[part] === saved.ver)) { text[part] = saved.text; ver[part] = saved.ver; continue; }
      try {
        const r = await gmReq({ method: 'GET', url: MODEL_URL + part + '.json?v=' + (remote ? remote[part] : Date.now()), timeout: 180000 });
        if (r.status !== 200 || r.responseText[0] !== '{') throw new Error('HTTP ' + r.status);
        text[part] = r.responseText;
        ver[part] = remote ? remote[part] : '?';
        modelDb('readwrite', (st) => st.put({ ver: ver[part], text: text[part] }, part)).catch(() => {});
      } catch (e) {
        if (saved && saved.text) { text[part] = saved.text; ver[part] = saved.ver; } // 新版本下载不了：先用存着的旧版本
        else { modelState = 'failed'; render(); setTimeout(loadModel, 30000); return; } // 过一会儿再试
      }
    }
    modelText = text;
    modelVer = ver;
    modelState = 'ready';
    if (cw) { cw.postMessage({ model: modelText }); cw.postMessage({ warm: true }); }
    render();
  }

  // ---------- 讲解放到后台线程（Web Worker）里生成：页面本身不会卡 ----------
  // 生成一段讲解要让两个网络算上亿次乘加，放在页面的主线程里，chess.com 会卡到算完为止。
  // 所以把脚本里“分析 + 措辞 + 两个网络”那几段代码原样取出来，放进一个后台线程里跑；
  // 主线程只管发请求、收结果。后台线程起不来或出错时，才退回在主线程里现算。
  const cwMark = (name) => '  // ' + '-'.repeat(10) + ' ' + name; // 段落标记（拼出来，免得这里的字样被当成标记）
  const CW_TIMEOUT = 20000;
  let cw = null, cwFailed = false;
  let lmNow = null; // 后台线程报告的：语言模型现在跑在哪（显卡上的完整网络 / CPU 上的小网络）
  const cwPending = new Map(); // 讲解的 key → { cache, at }
  const cwSkip = new Set();    // 后台线程生成失败过的讲解：改在主线程算

  // 后台线程里的入口（这个函数的源码会被拼到后台线程的代码末尾）
  function cwServe() {
    let chain = Promise.resolve();
    self.onmessage = (e) => { chain = chain.then(() => serve(e.data)); }; // 排队：一次只生成一段
    async function serve(q) {
      try {
        if (q.model) { setModel({ lm: JSON.parse(q.model.lm), nn: JSON.parse(q.model.nn) }); return; } // 主线程下载好的权重
        if (q.warm) { // 预热：把两个网络的权重解出来；有 WebGPU 就把完整的语言模型放到显卡上
          if (!LM || !NN_W) return;
          net(); lmNet();
          await lmGpuInit();
          self.postMessage({ info: lmInfo() });
          return;
        }
        if (q.probe) { self.postMessage({ probe: await lmProbe() }); return; }
        for (let attempt = 0; ; attempt++) {
          const S = makeSelector(q.c, q.key, q.recent, q.recentTexts, q.known);
          let last = null;
          S.emit = (text, solid) => { // 每生成一个词：把目前的全文发回去（solid = 其中已经定下来的长度）
            if (text === last) return;
            last = text;
            self.postMessage({ key: q.key, part: text, solid });
          };
          try {
            const paras = await (q.four ? compose4(q.c, W4_EN, S) : compose(q.c, W_EN, S));
            self.postMessage({ key: q.key, paras, used: S.used, texts: S.texts, learned: S.learned, tools: S.toolLog });
            return;
          } catch (err) {
            if (attempt || !err || err.message !== LM_GPU_LOST) throw err;
            self.postMessage({ info: lmInfo() }); // 显卡中途用不了了：这段用小网络重新生成
          }
        }
      } catch (err) {
        self.postMessage({ key: q.key, error: String((err && err.message) || err) });
      }
    }
  }

  function cwFail() {
    cwFailed = true;
    if (cw) { try { cw.terminate(); } catch (e) { /* 已经没了 */ } }
    cw = null;
    cwPending.clear();
    render();
  }

  function coachWorker() {
    if (cw || cwFailed) return cw;
    try {
      const src = coachMain.toString();
      const cut = (a, b) => {
        const i = src.indexOf(a), j = src.indexOf(b, i);
        if (i < 0 || j < 0) throw new Error('missing section');
        return src.slice(i, j);
      };
      const code = [
        "'use strict';",
        cut('  const LICHESS_URL', cwMark('界面文字')),            // 棋盘工具、战术识别、措辞库、两个网络、组句
        cut(cwMark('四人讲解用语'), cwMark('主循环')),            // 四人措辞库
        cut(cwMark('四人讲解：'), cwMark('四人模式的面板')),      // 四人组句
        `(${cwServe.toString()})();`,
      ].join('\n');
      cw = new Worker(URL.createObjectURL(new Blob([code], { type: 'application/javascript' })));
      cw.onmessage = (e) => {
        const r = e.data, q = cwPending.get(r.key);
        if (r.info) { lmNow = r.info; if (menuOpen) renderMenu(); return; }
        if (!q) return;
        if (r.part != null) { // 还在生成：目前的全文
          const first = !q.comp;
          q.comp = q.comp || { key: r.key, paras: [{ text: '' }], live: true };
          q.comp.paras[0].text = r.part;
          if (first) render(); // 第一个词到了：渲染一遍，开始打字
          streamShow(q, r.key, r.part, r.solid, false);
          return;
        }
        cwPending.delete(r.key);
        if (r.error) { cwSkip.add(r.key); render(); return; }
        const comp = q.comp || { key: r.key };
        comp.paras = r.paras;
        comp.live = false;
        comp.tools = (q.toolLog || []).concat(r.tools || []);
        (r.learned || []).forEach((t) => knownTerms.add(t));
        q.cache.set(r.key, comp);
        remember(r.used, r.texts);
        const full = r.paras.map((x) => x.text).join(' ');
        if (!q.four) noteMistake(q.c, full);
        streamShow(q, r.key, full, full.length, true);
        render(); // 生成完了：按钮等换成针对全文的
      };
      cw.onerror = cwFail;
      if (modelText) { cw.postMessage({ model: modelText }); cw.postMessage({ warm: true }); } // 权重还没下载好的话，下载完再发（见 loadModel）
    } catch (e) {
      cwFailed = true;
      cw = null;
    }
    return cw;
  }

  // 后台线程发来了这段讲解目前的全文：屏幕上显示的如果正是它，就接着往下显示、往下读
  function streamShow(q, key, text, solid, final) {
    if (!show || show.key !== key) return; // 屏幕上显示的不是它（已经翻到别的局面了）
    typeMore(text, !final);
    // 朗读：这段讲解第一次显示时开始；之后只往正在读的队列里续（用户按了停止就不再自己接着读）
    if (ttsAuto && (!q.spoke || (speakJob && speakJob.stream && speakJob.key === key))) {
      q.spoke = true;
      speakStream(key, text.slice(0, solid), final);
    }
  }

  // 取一段讲解：缓存里有就直接用；没有就交给后台线程生成（生成到哪显示到哪；还一个字都没有时返回 null）
  function composeVia(cache, key, c, four, direct) {
    let comp = cache.get(key);
    if (comp) return comp;
    if (modelState !== 'ready') return null; // 权重还没下载好
    const q = cwPending.get(key);
    if (q) {
      if (q.comp || Date.now() - q.at < CW_TIMEOUT) return q.comp || null; // 正在生成：有多少先给多少
      cwPending.delete(key); // 等太久了：这段改在主线程算
      cwSkip.add(key);
    }
    const w = cwSkip.has(key) ? null : coachWorker();
    if (w) {
      try {
        w.postMessage({ key, c, four, recent: recentIds, recentTexts, known: [...knownTerms] });
        cwPending.set(key, { cache, at: Date.now(), toolLog: c.toolLog, c, four });
        setTimeout(render, CW_TIMEOUT + 50);
        return null;
      } catch (e) { cwSkip.add(key); } // 这段素材传不过去：在主线程算
    }
    // 后台线程用不了：在主线程算（小网络）。生成是异步的，先返回 null，算完再刷新
    if (!LM || !NN_W) setModel({ lm: JSON.parse(modelText.lm), nn: JSON.parse(modelText.nn) });
    const S = makeSelector(c, key, recentIds, recentTexts, [...knownTerms]);
    cwPending.set(key, { cache, at: Date.now(), toolLog: c.toolLog, c, four });
    Promise.resolve().then(() => direct(S)).then((paras) => {
      cache.set(key, { key, paras, tools: (c.toolLog || []).concat(S.toolLog) });
      S.learned.forEach((t) => knownTerms.add(t));
      remember(S.used, S.texts);
      if (!four) noteMistake(c, paras.map((x) => x.text).join(' '));
    }).catch(() => { cache.set(key, { key, paras: [{ text: L().noEval }] }); }).then(() => { cwPending.delete(key); render(); });
    return null;
  }

  function composeCached(c) {
    return composeVia(compCache, c.seed, c, false, (S) => compose(c, W_EN, S));
  }

  // ---------- 朗读：浏览器语音合成，自动挑最像真人的声音 ----------
  // Edge 里有微软的“自然语音”（Ava、Andrew 等：在线、免费、最像真人）；Chrome 里是 Google 的在线语音。
  let ttsAuto = GM_getValue('cwp_tts', true);
  const ttsVoice = GM_getValue('cwp_voice', {}); // { en: 声音名 }；没选过就自动挑
  let speaking = false;
  const synth = window.speechSynthesis;
  // 声音质量排序参考 Readium Speech 整理的质量表（github.com/readium/speech/tree/main/json）：
  // 最高 = 微软在线“自然语音”（Edge 浏览器自带，免费）；其次 Google 在线语音（Chrome）；再其次 macOS 的高质量语音
  const VOICE_RANK = [/(Ava|Emma|Andrew|Brian)Multilingual.*Natural/i, /(Jenny|Aria|Guy|Michelle|Christopher|Eric|Roger|Steffan).*Natural/i, /Natural/i,
    /Google US English/i, /Google UK English/i, /^(Ava|Zoe)\b/i, /Premium|Enhanced/i, /Alex|Samantha|Allison/i];
  const isTopVoice = (v) => !!v && /Natural/i.test(v.name); // 最高一档：微软在线自然语音

  function voicesFor() {
    if (!synth) return [];
    const rank = (v) => { const i = VOICE_RANK.findIndex((re) => re.test(v.name)); return i < 0 ? 99 : i; };
    return synth.getVoices().filter((v) => v.lang.toLowerCase().startsWith('en')).sort((a, b) => rank(a) - rank(b));
  }
  const pickVoice = () => { const vs = voicesFor(); return vs.find((v) => v.name === ttsVoice.en) || vs[0] || null; };

  // ---------- 讲解的呈现：一边生成，一边显示，一边朗读；文字和朗读各走各的 ----------
  // 文字：后台线程每生成一个词，目标文字就变长一点；屏幕上按固定节奏连贯地一个字一个字冒出来（不会超过已生成的部分）。
  //       朗读开着时，文字先等声音开口，两边一起开始（见 voiceHold）；开始之后文字按自己的速度出，不再等声音；
  // 朗读：每生成完一句就马上排进朗读队列，不等整段生成完；一句之内一口气读，保留自然的语调和停顿。
  const shownKeys = new Set(); // 已经打完字的讲解，再显示时直接给全文
  let show = null;             // 正在打字的讲解 { key, full, shown, el, timer, live }（live = 还在生成，full 还会变长）
  let speakJob = null;         // 正在朗读的讲解 { key, utters, … }（留着引用：Chrome 可能提前回收朗读对象）
  const TTS_HOLD = 2000;       // 文字最多等声音这么久（毫秒）
  let ttsLate = false;         // 上一段讲解的声音没能及时开口（没网、读不了等）：文字先不等了，直到声音又能及时开口

  // 按句子切开，切出来的片段拼回去和原文一模一样（英文的小数点不切）
  function splitKeep(t) {
    const out = [];
    let st = 0;
    for (let i = 0; i < t.length; i++) {
      if ('!?;'.includes(t[i]) || (t[i] === '.' && (i + 1 === t.length || /\s/.test(t[i + 1])))) {
        let j = i + 1;
        while (j < t.length && /\s/.test(t[j])) j++;
        out.push(t.slice(st, j));
        st = j;
        i = j - 1;
      }
    }
    if (st < t.length) out.push(t.slice(st));
    return out;
  }

  function paint() {
    if (show && show.el) show.el.textContent = show.full.slice(0, show.shown) + (show.shown < show.full.length || show.live ? '▍' : '');
  }

  // 朗读开着时，文字等声音开口再出，两边一起开始：这段讲解的朗读已经在准备、但还没出声，就先不出字。
  // 只等开头这一下，最多等 TTS_HOLD；声音开口之后文字按自己的速度连贯地出，不跟着朗读的节奏
  function voiceHold(key) {
    const job = speakJob;
    if (!job || job.key !== key || job.started || ttsLate) return false;
    if (performance.now() - job.at < TTS_HOLD) return true;
    ttsLate = true; // 等到头了还没出声：这段不等了，后面的讲解也先不等
    return false;
  }

  // 声音开口了（failed：出错读不了）：等着的文字可以出了
  function voiceBegan(job, failed) {
    if (job.started) return;
    job.started = true;
    ttsLate = !!failed || performance.now() - job.at > TTS_HOLD;
  }

  function typeText(key, full, el, live) {
    if (show) clearInterval(show.timer);
    const s = show = { key, full, shown: 0, el, live: !!live };
    paint();
    s.timer = setInterval(() => {
      if (voiceHold(s.key)) return;
      s.shown = Math.min(s.full.length, s.shown + 3 + (Math.random() < 0.25 ? 1 : 0));
      if (show === s) paint();
      if (s.shown >= s.full.length && !s.live) { clearInterval(s.timer); shownKeys.add(s.key); } // 还在生成的话，停在这等后面的词
    }, 30);
  }

  // 讲解还在生成：目标文字换成最新的全文。正在生成的那一句如果被推翻重写，已显示的部分退回到两版相同的开头
  function typeMore(text, live) {
    const s = show, m = Math.min(s.full.length, text.length);
    let n = 0;
    while (n < m && s.full[n] === text[n]) n++;
    s.shown = Math.min(s.shown, n);
    s.full = text;
    s.live = live;
    paint();
  }

  function stopSpeech() {
    speakJob = null;
    if (synth) synth.cancel();
    speaking = false;
  }

  // 整段朗读（▶ 按钮，或者讲解一出来就是完整的）：和边生成边朗读走同一条路，只是一次把全文交过去
  function speakText(key, text) {
    if (!synth) return;
    stopSpeech();
    speakStream(key, text, true);
  }

  // 边生成边朗读：solid 是讲解里已经定下来的部分。每多出完整的句子就马上排进朗读队列，不等整段生成完；
  // 一次多出几句就合成一段读（Chrome 的 Google 在线语音除外，它读长段会中途断掉，仍然一句一句排，中间不额外等待）。
  function speakStream(key, solid, final) {
    if (!synth) return;
    let job = speakJob;
    if (!job || job.key !== key || !job.stream) {
      stopSpeech();
      job = speakJob = { key, stream: true, utters: [], queue: [], pos: 0, left: 0, final: false, ready: false, started: false, at: performance.now(), voice: pickVoice() };
      speaking = true;
      setTimeout(() => { if (speakJob === job) { job.ready = true; flush(); } }, 120); // Chrome：刚取消就立刻开始朗读，偶尔会吞掉第一句
    }
    if (job.final) return;
    job.final = final;
    // 新定下来的文字里，到最后一个句末标点为止的部分可以读了；生成完了就全读
    const pieces = splitKeep(solid.slice(job.pos));
    if (!final && pieces.length && !/[!?;.]\s*$/.test(pieces[pieces.length - 1])) pieces.pop();
    const text = pieces.join('');
    job.pos += text.length;
    const google = job.voice && /Google/i.test(job.voice.name);
    (google ? pieces : [text]).map((x) => x.trim()).filter(Boolean).forEach((x) => job.queue.push(x));
    flush();

    function flush() {
      if (!job.ready || speakJob !== job) return;
      const end = () => { // 全部读完（或出错）：按钮变回 ▶
        if (speakJob === job && job.final && job.left <= 0 && !job.queue.length) { speakJob = null; speaking = false; render(); }
      };
      if (!google && job.queue.length > 1) job.queue = [job.queue.join(' ')]; // 攒了几句：合成一段读，语调更连贯
      while (job.queue.length) {
        const u = new SpeechSynthesisUtterance(job.queue.shift()), v = job.voice;
        if (v) { u.voice = v; u.lang = v.lang; } else u.lang = 'en-US';
        u.rate = opts.ttsRate; // 朗读速度：在菜单的 Settings 里改
        job.left++;
        u.onstart = () => voiceBegan(job);
        u.onend = () => { voiceBegan(job); job.left--; end(); };
        u.onerror = (e) => { job.left--; if (e.error !== 'interrupted' && e.error !== 'canceled') { voiceBegan(job, true); end(); } };
        job.utters.push(u);
        synth.speak(u);
      }
      end();
    }
  }

  function stopPresent() {
    if (show) {
      clearInterval(show.timer);
      shownKeys.add(show.key);
      show = null;
    }
    stopSpeech();
  }
  const stopSpeak = stopPresent;

  function present(key, full, el, withVoice, live) {
    stopPresent();
    typeText(key, full, el, live);
    if (withVoice) speakText(key, full);
  }

  if (synth) synth.addEventListener('voiceschanged', () => render());

  // ---------- 评估换算 ----------
  function winW(a) { // 白方胜率 %
    if (a.over === 'mate') return a.turn === 'w' ? 0 : 100;
    if (a.over === 'draw') return 50;
    if (a.mateW != null) return a.mateW > 0 ? 100 : 0;
    if (a.cpW == null) return 50;
    return 50 + 50 * (2 / (1 + Math.exp(-0.00368208 * a.cpW)) - 1); // Lichess 公式
  }
  const winFor = (a, c) => (c === 'w' ? winW(a) : 100 - winW(a));
  const stateOf = (w) => (w >= 90 ? 'winning' : w >= 65 ? 'better' : w > 35 ? 'equal' : w > 10 ? 'worse' : 'losing');

  function evalText(a) {
    if (a.over === 'mate') return a.turn === 'w' ? '0-1 #' : '1-0 #';
    if (a.over === 'draw') return '½-½';
    if (a.mateW != null) return (a.mateW > 0 ? '+M' : '-M') + Math.abs(a.mateW);
    if (a.cpW == null) return '…';
    const v = a.cpW / 100;
    return (v > 0 ? '+' : '') + v.toFixed(1);
  }

  function subText(a) {
    const T = L();
    if (a.error) return T[a.error];
    if (a.over === 'mate') return T.matedWin(a.turn === 'w' ? T.black : T.white);
    if (a.over === 'draw') return T.stalemate;
    if (a.mateW != null) return T.mateIn(a.mateW > 0 ? T.white : T.black, Math.abs(a.mateW));
    if (a.cpW == null) return T.analysing;
    const c = Math.abs(a.cpW), side = a.cpW > 0 ? T.white : T.black;
    if (c < 30) return T.even;
    if (c < 100) return T.slight(side);
    if (c < 250) return T.clear(side);
    return T.winning(side);
  }

  const pct = (x) => Math.round(x) + '%';

  // ---------- 讲解素材：这步做了什么、错在哪、更好的是什么 ----------
  // 威胁分析（空着法）：nullE 是“让 who 连走一步”的局面的评估，base 是原局面的。能很快将杀、或者能赢子，才算威胁
  function threatOf(nullE, base, who) {
    if (!nullE || !nullE.done || nullE.error || nullE.over || !nullE.pv || !nullE.pv.length) return null;
    const line = playLine(parseBoard(nullE.fen), nullE.pv, 4), m = line.moves[0];
    if (!m) return null;
    const mate = nullE.mateW != null && (who === 'w' ? nullE.mateW > 0 : nullE.mateW < 0) ? Math.abs(nullE.mateW) : null;
    const gain = lineMat(line, who, 4), jump = winFor(nullE, who) - winFor(base, who);
    if (mate && mate <= 3) return { m, mate, gain };
    if (gain >= 1 && jump >= 8) return { m, mate: null, gain };
    return null;
  }

  function buildCtx(pair) {
    const { prev: before, cur: after, move } = pair;
    const me = move.mover;
    const wb = winFor(before, me), wa = winFor(after, me), loss = Math.max(0, wb - wa);
    const bBefore = parseBoard(before.fen), bAfter = parseBoard(after.fen);
    const myMate = (a) => (a.mateW != null && (me === 'w' ? a.mateW > 0 : a.mateW < 0) ? Math.abs(a.mateW) : null);
    const oppMate = (a) => (a.mateW != null && (me === 'w' ? a.mateW < 0 : a.mateW > 0) ? Math.abs(a.mateW) : null);
    const cpMe = (a) => (a.cpW == null || a.over ? null : (me === 'w' ? a.cpW : -a.cpW) / 100);
    const phase = phaseOf(bBefore, before.fen, !/ 0 1$/.test(before.fen));

    // 查知识库：这步之后的局面有没有开局名称（没有就看走之前的——对手刚走成的开局也提一句）；是不是这一步刚进入某个基本残局
    const toolLog = [];
    let opening = null, endgame = null;
    if (phase === 'opening') {
      const op = callTool('opening_lookup', { fen: after.fen }, toolLog) || callTool('opening_lookup', { fen: before.fen }, toolLog);
      opening = op ? op.name : null;
    }
    if (phase === 'endgame') {
      const eg = callTool('endgame_lookup', { fen: after.fen }, toolLog), was = eg && callTool('endgame_lookup', { fen: before.fen }, toolLog);
      if (eg && !(was && was.name === eg.name) && (eg.verdict === 'draw' || (eg.strong === me && wa >= 90))) endgame = eg;
    }

    const played = moveInfo(bBefore, move.uci);
    const isBest = before.best === move.uci;
    const best = before.best && !isBest ? moveInfo(bBefore, before.best) : null;
    const replyLine = after.over ? { moves: [], boards: [bAfter] } : playLine(bAfter, after.pv, 7);
    const bestLine = best ? playLine(bBefore, before.pv, 7) : { moves: [], boards: [bBefore] };
    const reply = replyLine.moves[0] || null; // 对手的最佳应对
    // 查知识库：这步将杀（或者这步之后对方一步杀）是不是有名字的将杀
    const mateOf = (board, uci) => { const r = callTool('mate_pattern_lookup', { position: board, move: uci, opening: phase === 'opening' }, toolLog); return r ? r.entry : null; };
    const matePattern = after.over === 'mate' ? mateOf(bAfter, move.uci) : reply && oppMate(after) === 1 ? mateOf(reply.after, reply.uci) : null;

    // 对手吃子后我方能不能吃回来：净损失 ≥ 2 才算“送子/弃子”
    let freeLoss = 0;
    if (reply && reply.cap) {
      const recap = replyLine.moves[1];
      const back = recap && recap.to === reply.to && recap.cap ? VAL[recap.cap] : 0;
      freeLoss = VAL[reply.cap] - back;
    }
    const replyMat = lineMat(replyLine, me, 4);

    // 威胁分析（空着法）：走之前对方想干什么；走之后这步想干什么
    const oppThreat = threatOf(pair.prevNull, before, other(me));
    const myThreat = after.over ? null : threatOf(pair.curNull, after, me);

    const mateBefore = myMate(before), mateAfter = myMate(after);
    let kind;
    if (after.over === 'mate') kind = 'mate';
    else if (mateBefore && !mateAfter) kind = 'missedMate';
    else if (mateAfter && (isBest || loss < 5)) kind = 'mating';
    else if (isBest) kind = 'best';
    else if (loss < 2) kind = 'excellent';
    else if (loss < 5) kind = 'good';
    else if (loss < 10) kind = 'inaccuracy';
    else if (loss < 20) kind = 'mistake';
    else kind = 'blunder';

    // 化解了威胁：原来对方能赢的子（或杀棋），走完这步之后拿不到了
    const parried = !!oppThreat && !oppMate(after) && (oppThreat.mate ? true : -replyMat < oppThreat.gain - 0.5);
    return {
      me, kind, played, best, reply, replyLine, bestLine, wb, wa, loss, phase,
      oppThreat, myThreat, parried, ignored: !!oppThreat && !parried && BAD.includes(kind),
      tags: analyzeMove(bBefore, played, phase),
      replyTags: reply ? analyzeMove(bAfter, reply, phase) : [], // 对手的最佳回应要干什么（双击、牵制……）
      bestTags: best ? analyzeMove(bBefore, best, phase) : [],
      cpB: cpMe(before), cpA: cpMe(after),
      stBefore: stateOf(wb), stAfter: stateOf(wa),
      mateBefore, mateAfter, oppMateAfter: oppMate(after),
      replyMat,
      playedGain: matBal(bAfter, me) - matBal(bBefore, me) + replyMat,
      bestGain: best ? lineMat(bestLine, me, 4) : 0,
      sacrifice: !!reply && reply.to === played.to && freeLoss - (played.cap ? VAL[played.cap] : 0) >= 2 && loss < 5,
      hanging: freeLoss - (reply && reply.to === played.to && played.cap ? VAL[played.cap] : 0) >= 2,
      seed: before.fen + move.uci, fen: before.fen,
      opening, endgame, matePattern, toolLog,
    };
  }

  // ---------- 渲染 ----------
  function render() {
    const T = L();
    $('.ttl').textContent = T.title;
    $('.min-btn').title = T.collapse;
    const me = mySide();
    $('.side').textContent = (me === 'w' ? '♔ ' : '♚ ') + T.side[sideMode];
    $('.side').title = T.sideTip;
    $('.tts').textContent = ttsAuto ? '🔊' : '🔇';
    $('.tts').title = T.ttsTip;
    $('.menu-btn').title = menuOpen ? T.menu.close : T.menu.open;
    if (isFour()) { render4(T); return; }
    $('.side').style.display = '';
    $('.bar').style.background = '';
    $('.bar .w').style.background = '';
    $('.lw').style.color = $('.lb').style.color = '';

    if (!cur) { $('.sub').textContent = T.waiting; $('.st').textContent = ''; return; }
    $('.st').textContent = cur.done ? (cur.src ? T[cur.src] : '') : cur.src === 'local' ? T.localRunning : T.fetching;

    const w = winW(cur);
    const ev = $('.ev');
    ev.textContent = evalText(cur);
    ev.style.color = w > 55 ? '#f0f0f0' : w < 45 ? '#9e9b98' : '#e8e6e3';
    $('.sub').textContent = subText(cur) + (cur.depth ? T.depth(cur.depth) : '');
    $('.bar .w').style.width = w.toFixed(1) + '%';
    $('.lw').textContent = pct(w);
    $('.lb').textContent = pct(100 - w);

    // 对手刚走完：提示一下，但保留你上一步的讲解
    let note = '';
    if (lastMove && lastMove.mover !== me && prev) {
      const m = moveInfo(parseBoard(prev.fen), lastMove.uci);
      if (m) note = T.oppMoved(T.W.move(m));
    }
    $('.nt').textContent = note;

    const pair = pairs[me];
    let cls = '#666', title, paras, change = '';
    curComp = null;
    // 威胁分析要多查两个“空着法”局面：走之前轮到对方、走之后轮到自己
    const nb = pair && nullFen(pair.prev.fen), na = pair && nullFen(pair.cur.fen);
    const nullB = nb ? evalOf(nb) : null, nullA = na ? evalOf(na) : null;
    if (!pair) { title = T.promptT; paras = [{ text: T.prompt }]; }
    else if (modelState !== 'ready') { title = T.modelT; paras = [{ text: modelState === 'failed' ? T.modelFail : T.modelLoading }]; }
    else if (!evalOf(pair.prev.fen).done || !evalOf(pair.cur.fen).done || (nullB && !nullB.done) || (nullA && !nullA.done)) { title = T.thinkingT; paras = [{ text: T.thinking }]; }
    else if (pair.prev.error || pair.cur.error) { title = T.noEvalT; paras = [{ text: T.noEval }]; }
    else {
      const c = buildCtx({ ...pair, prevNull: nullB, curNull: nullA });
      cls = COLORS[c.kind];
      title = T.labels[c.kind];
      curComp = composeCached(c);
      paras = curComp ? curComp.paras : [{ text: '▍' }]; // 讲解还在后台线程里生成，第一个词马上就来
      change = T.change(pct(c.wb), pct(c.wa));
    }
    renderComment(T, cls, title, paras, change);
    updateMarks(me, pair);
  }

  // 讲解框（普通象棋和四人象棋共用）：逐字显示、自动朗读、声音选择
  function renderComment(T, cls, title, paras, change) {
    $('.cm').style.borderLeftColor = cls;
    $('.ct').textContent = title;
    // 这段讲解查知识库查到了什么（鼠标停在评级上能看到）
    const found = ((curComp && curComp.tools) || []).filter((t) => t.result && !t.result.draw).map((t) => `${t.tool} → ${t.result.name || t.result.entry}`);
    $('.ct').title = found.length ? 'Knowledge base: ' + found.join('; ') : '';
    $('.ct').style.color = cls;
    const cx = $('.cx');
    cx.textContent = '';
    const full = paras.map((p) => p.text).join(' ');
    const el = document.createElement('p');
    cx.appendChild(el);
    if (curComp && show && show.key === curComp.key) { show.el = el; paint(); }                // 正在呈现：接着来
    else if (curComp && !shownKeys.has(curComp.key)) present(curComp.key, full, el, ttsAuto && !curComp.live, curComp.live); // 新讲解：边读边显示（还在生成的，朗读由 streamShow 一句句排）
    else {
      if (show) stopPresent(); // 显示的讲解换了（或变成“思考中”）：正在读的立刻停
      el.textContent = full;
    }

    // 底部：▶/⏹（重读 / 停止朗读）和声音选择
    const fb = $('.fb');
    fb.textContent = '';
    panel.querySelectorAll('.vhint').forEach((h) => h.remove());
    if (curComp) {
      const btn = document.createElement('button');
      btn.textContent = speaking ? '⏹' : '▶️';
      btn.title = speaking ? T.stop : T.read;
      btn.addEventListener('click', () => { // 只控制朗读；文字已经显示出来了
        if (speaking) stopSpeech();
        else speakText(curComp.key, full);
        render();
      });
      const sel = document.createElement('select');
      sel.title = T.voiceTip;
      const vs = voicesFor(), cur = pickVoice();
      if (!vs.length) sel.appendChild(new Option(T.noVoice, ''));
      vs.forEach((v, i) => sel.appendChild(new Option((i === 0 ? '★ ' : '') + v.name, v.name, false, cur && v.name === cur.name)));
      sel.addEventListener('change', () => {
        ttsVoice.en = sel.value;
        GM_setValue('cwp_voice', ttsVoice);
      });
      fb.append(btn, sel);
      if (vs.length && !vs.some(isTopVoice)) { // 没有最高一档的声音：提示用 Edge
        const hint = document.createElement('div');
        hint.className = 'vhint';
        hint.textContent = T.edgeHint;
        fb.after(hint);
      }
    }
    if (document.querySelectorAll('#cwp').length > 1) { // 旧版插件也在运行：会重复朗读、内容错位
      const warn = document.createElement('div');
      warn.className = 'vhint';
      warn.style.color = '#fa412d';
      warn.textContent = T.dupWarn;
      fb.after(warn);
    }
    $('.cn').textContent = change;
  }

  // ---------- 菜单、错题本和棋盘标注 ----------
  // 小工具：造一个页面元素 / 一个 SVG 元素
  const h = (tag, attrs, ...kids) => {
    const el = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs || {})) {
      if (k.startsWith('on')) el.addEventListener(k.slice(2), v);
      else if (k === 'class') el.className = v;
      else if (v != null && v !== false) el.setAttribute(k, v);
    }
    el.append(...kids.filter((x) => x != null && x !== false));
    return el;
  };
  const sv = (tag, attrs) => {
    const el = document.createElementNS('http://www.w3.org/2000/svg', tag);
    for (const k in attrs) el.setAttribute(k, attrs[k]);
    return el;
  };

  // 错题本：你走错的每一步都记下来（疑问手可以在设置里关掉），保留 30 天
  const BOOK_DAYS = 30, BOOK_MAX = 400;
  const bookFresh = (list) => list.filter((m) => Date.now() - m.t < BOOK_DAYS * 864e5).slice(0, BOOK_MAX);
  let book = bookFresh(GM_getValue('cwp_book', []));

  function noteMistake(c, text) {
    if (!c || !c.fen || !c.played || !BAD.includes(c.kind) || (c.kind === 'inaccuracy' && !opts.bookInacc)) return;
    if (book.some((m) => m.id === c.seed)) return;
    const W = L().W, tactic = c.reply && c.replyTags.some((t) => ['fork', 'pin', 'skewer', 'discovered'].includes(t.t));
    const why = c.kind === 'missedMate' ? 'missedMate' : c.oppMateAfter ? 'mate' : c.hanging ? 'hanging' : c.ignored ? 'ignored' : tactic ? 'tactic' : 'other';
    book = bookFresh([{
      id: c.seed, t: Date.now(), fen: c.fen, uci: c.played.uci, move: W.move(c.played), kind: c.kind, side: c.me,
      wb: Math.round(c.wb), wa: Math.round(c.wa), best: c.best ? c.best.uci : null, why, text,
    }, ...book]);
    GM_setValue('cwp_book', book);
    if (menuOpen && menuPage !== 'settings') renderMenu();
  }

  // 菜单：左边一列栏目，右边是内容。要加新栏目，往 MENU 里添一项、写一个画内容的函数就行
  const MENU = [
    { id: 'overview', icon: '📊', draw: pageOverview },
    { id: 'mistakes', icon: '📕', draw: pageMistakes },
    { id: 'settings', icon: '⚙️', draw: pageSettings },
  ];
  const MENU_W = 660;
  let menuOpen = false, menuPage = 'overview', menuShift = 0, bookOpen = null, clearArmed = false;

  function toggleMenu(on) {
    menuOpen = on;
    panel.classList.add('anim'); // 只在开合的这一下让宽度和位置带过渡（拖动面板时不带）
    setTimeout(() => panel.classList.remove('anim'), 340);
    const left = parseInt(panel.style.left) || 0;
    if (on) { // 变宽后不能伸出屏幕右边：需要的话整个面板往左让，关上时再让回去
      const to = Math.max(0, Math.min(left, window.innerWidth - MENU_W - 10));
      menuShift = left - to;
      panel.style.left = to + 'px';
      panel.classList.remove('min');
      renderMenu(true);
    } else {
      panel.style.left = left + menuShift + 'px';
      menuShift = 0;
    }
    panel.classList.toggle('menu', on);
    $('.menu-btn').textContent = on ? '✕' : '☰';
    render();
  }

  function renderMenu(top) {
    const T = L().menu, nav = $('.nav'), pg = $('.pg'), keep = top ? 0 : pg.scrollTop;
    nav.textContent = '';
    MENU.forEach((m) => nav.append(h('button', { class: m.id === menuPage ? 'on' : '', onclick: () => { menuPage = m.id; clearArmed = false; renderMenu(true); } }, h('span', null, m.icon), T.nav[m.id])));
    pg.textContent = '';
    MENU.find((m) => m.id === menuPage).draw(pg, T);
    pg.scrollTop = keep;
  }

  // 概览：近 30 天走错了多少、最常错在哪、现在用的引擎和声音
  function pageOverview(pg, T) {
    const n = (f) => book.filter(f).length;
    pg.append(h('h3', null, T.overviewT), h('div', { class: 'cards' },
      ...[[book.length, T.total], [n((m) => m.kind === 'blunder' || m.kind === 'missedMate'), T.blunders], [n((m) => m.kind === 'mistake'), T.mistakes], [n((m) => m.kind === 'inaccuracy'), T.inaccs]]
        .map(([v, label]) => h('div', { class: 'card' }, h('b', null, String(v)), h('span', null, label)))));
    const whys = Object.keys(T.why).map((k) => [k, n((m) => m.why === k)]).filter((x) => x[1]).sort((a, b) => b[1] - a[1]);
    pg.append(h('h4', null, T.weakT));
    if (!whys.length) pg.append(h('div', { class: 'dim' }, T.noData));
    whys.forEach(([k, v]) => pg.append(h('div', { class: 'wk' }, h('span', null, T.why[k]), h('i', null, h('u', { style: `width:${Math.round(v / whys[0][1] * 100)}%` })), h('b', null, String(v)))));
    if (whys.length) pg.append(h('div', { class: 'tipbox' }, T.focus[whys[0][0]]));
    const v = pickVoice(), ver = typeof GM_info !== 'undefined' && GM_info.script ? GM_info.script.version : '–';
    pg.append(h('h4', null, T.statusT), h('div', { class: 'kv' },
      ...[[T.engine, cur && cur.src ? L()[cur.src] : '–'], [T.localEngine, T.sf[sfState]], [T.lm, lmNow ? (lmNow.gpu ? T.lmGpu : T.lmCpu)((lmNow.params / 1e6).toFixed(1)) : '–'], [T.model, modelVer ? `lm ${modelVer.lm} · nn ${modelVer.nn}` : modelState], [T.voice, v ? v.name : L().noVoice], [T.version, ver]]
        .flatMap(([k, val]) => [h('span', null, k), h('b', null, val)])));
  }

  // 错题本里的小棋盘：走这步之前的局面，红箭头是你走的，绿箭头是更好的走法
  const GLYPH = { k: '♚', q: '♛', r: '♜', b: '♝', n: '♞', p: '♟' };
  function miniBoard(m) {
    const flip = m.side === 'b', b = parseBoard(m.fen), box = h('div', { class: 'mb' });
    for (let row = 0; row < 8; row++) {
      for (let col = 0; col < 8; col++) {
        const f = flip ? 7 - col : col, r = flip ? row : 7 - row, p = b[FILES[f] + (r + 1)];
        box.append(h('i', { class: (f + r) % 2 ? 'l' : 'd' }, p ? h('b', { class: colorOf(p) }, GLYPH[p.toLowerCase()]) : null));
      }
    }
    const svg = sv('svg', { viewBox: '0 0 8 8' });
    svg.append(arrowEl(sqPt(m.uci.slice(0, 2), flip), sqPt(m.uci.slice(2, 4), flip), MARK_COLORS.red));
    if (m.best) svg.append(arrowEl(sqPt(m.best.slice(0, 2), flip), sqPt(m.best.slice(2, 4), flip), MARK_COLORS.green));
    box.append(svg);
    return box;
  }

  // 把错题本整理成一段文字：贴到任何一个 AI 对话里都能看懂（走之前的局面、你走的、引擎更想走的、胜率变化、当时的讲解）
  function bookText() {
    const T = L(), out = [`My chess mistakes from the last ${BOOK_DAYS} days (${book.length} moves), recorded by the Chess.com Coach userscript. Each entry has the position before my move (FEN), the move I played, the move the engine preferred, my win chance before and after, and the coach's comment.`];
    book.forEach((m, i) => out.push('',
      `${i + 1}. ${new Date(m.t - new Date(m.t).getTimezoneOffset() * 6e4).toISOString().slice(0, 10)} · ${T.labels[m.kind].replace(/^\S+ /, '')} · I was ${m.side === 'w' ? 'White' : 'Black'}`,
      `   FEN: ${m.fen}`,
      `   Played: ${m.uci} (${m.move})${m.best ? ` · Engine preferred: ${m.best}` : ''} · Win chance ${m.wb}% → ${m.wa}%`,
      `   Problem: ${T.menu.why[m.why] || ''}`,
      `   Coach: ${m.text}`));
    return out.join('\n');
  }
  function copyText(t) {
    if (typeof GM_setClipboard === 'function') GM_setClipboard(t);
    else if (navigator.clipboard) navigator.clipboard.writeText(t).catch(() => {});
  }

  function pageMistakes(pg, T) {
    const copy = h('button', { class: 'copy', title: T.copyTip, onclick: () => { copyText(bookText()); copy.textContent = T.copied; setTimeout(() => { copy.textContent = T.copy; }, 1500); } }, T.copy);
    pg.append(h('h3', null, T.mistakesT(book.length), book.length ? copy : null));
    if (!book.length) { pg.append(h('div', { class: 'dim' }, T.noData)); return; }
    const day = (t) => { const d = new Date(t); return new Date(d.getFullYear(), d.getMonth(), d.getDate()).getTime(); };
    const today = day(Date.now());
    let last = null;
    book.forEach((m) => {
      const d = day(m.t), open = bookOpen === m.id;
      if (d !== last) {
        last = d;
        pg.append(h('div', { class: 'dayh' }, d === today ? T.today : d === day(today - 1) ? T.yesterday : new Date(d).toLocaleDateString('en-US', { month: 'short', day: 'numeric' })));
      }
      const row = h('div', { class: 'mk' },
        h('div', { class: 'mkh', onclick: () => { bookOpen = open ? null : m.id; renderMenu(); } },
          h('span', { class: 'tag', style: `background:${COLORS[m.kind]}` }, L().labels[m.kind].split(' ')[0]),
          h('span', { class: 'mv' }, m.move), h('span', { class: 'dr' }, `${m.wb}% → ${m.wa}%`), h('span', { class: 'ar' }, open ? '▾' : '▸')));
      if (open) {
        row.append(h('div', { class: 'mkb' }, miniBoard(m), h('div', { class: 'mkt' },
          h('div', { class: 'why' }, T.why[m.why] || ''), h('p', null, m.text),
          h('div', { class: 'lnk' },
            h('a', { href: 'https://www.chess.com/analysis?fen=' + encodeURIComponent(m.fen), target: '_blank', rel: 'noopener' }, T.openPos),
            h('a', { href: '#', onclick: (e) => { e.preventDefault(); book = book.filter((x) => x.id !== m.id); GM_setValue('cwp_book', book); renderMenu(); } }, T.remove)))));
      }
      pg.append(row);
    });
  }

  function pageSettings(pg, T) {
    // 开关：key 是 opts 里的一项；也可以自己给读写函数（朗读开关不存在 opts 里）
    const sw = (key, label, desc, off, get, set) => {
      const box = h('input', { type: 'checkbox' });
      box.checked = get ? get() : opts[key];
      box.disabled = !!off;
      box.addEventListener('change', () => { if (set) set(box.checked); else setOpt(key, box.checked); render(); renderMenu(); });
      return h('label', { class: 'opt' + (off ? ' off' : '') }, h('div', null, h('b', null, label), desc ? h('small', null, desc) : null), h('span', { class: 'sw' }, box, h('i')));
    };
    const pick = (label, options, value, onpick) => {
      const sel = h('select');
      options.forEach(([v, text]) => sel.append(new Option(text, v, false, v === value)));
      sel.addEventListener('change', () => { onpick(sel.value); render(); });
      return h('label', { class: 'opt' }, h('div', null, h('b', null, label)), sel);
    };
    // 朗读速度：自己输入数字（0.5–3）；输入的不是数字就恢复原来的值
    const rate = h('input', { type: 'text', inputmode: 'decimal', class: 'num' });
    rate.value = opts.ttsRate;
    rate.addEventListener('change', () => {
      const x = parseFloat(rate.value);
      if (isFinite(x)) setOpt('ttsRate', Math.round(Math.max(0.5, Math.min(3, x)) * 100) / 100);
      rate.value = opts.ttsRate;
    });
    const vs = voicesFor(), v = pickVoice(), noMarks = !opts.marks;
    pg.append(h('h3', null, T.settingsT),
      h('h4', null, T.gRead),
      sw(null, T.sTts, null, false, () => ttsAuto, (on) => { ttsAuto = on; GM_setValue('cwp_tts', on); if (!on) stopSpeak(); }),
      h('label', { class: 'opt' }, h('div', null, h('b', null, T.sRate), h('small', null, T.sRateD)), rate),
      pick(T.sVoice, vs.length ? vs.map((x, i) => [x.name, (i === 0 ? '★ ' : '') + x.name]) : [['', L().noVoice]], v ? v.name : '', (name) => { ttsVoice.en = name; GM_setValue('cwp_voice', ttsVoice); }),
      pick(T.sSide, Object.entries(L().side), sideMode, (m) => { sideMode = m; GM_setValue('cwp_side', m); }),
      h('h4', null, T.gMarks),
      sw('marks', T.sMarks, T.sMarksD), sw('markAnimate', T.sAnim, T.sAnimD, noMarks), sw('markThreats', T.sThreats, T.sThreatsD, noMarks), sw('markBetter', T.sBetter, T.sBetterD, noMarks),
      h('h4', null, T.gBook),
      sw('bookInacc', T.sInacc, T.sInaccD),
      h('button', { class: 'danger', onclick: () => { if (clearArmed) { book = []; GM_setValue('cwp_book', book); } clearArmed = !clearArmed; renderMenu(); } }, clearArmed ? T.clearSure : T.clear));
  }

  // 棋盘标注：照着“标注工具”（board_arrow / board_circle）的调用记录，在棋盘上画箭头、圈格子。
  // 画在棋盘元素里单独的一层上（不挡鼠标）；坐标用 8×8 的格子，棋盘翻转时跟着翻
  const sqPt = (sq, flip) => { const [x, y] = sqXY(sq); return flip ? [7.5 - x, y + 0.5] : [x + 0.5, 7.5 - y]; };

  // 箭头：set(p) 画到全长的 p 成（0–1），返回箭头尖现在的位置（动画时光标跟着它走）
  function arrowEl(a, b, color) {
    const g = sv('g', { opacity: 0.85 }), line = sv('line', { stroke: color, 'stroke-width': 0.17, 'stroke-linecap': 'round' }), head = sv('polygon', { fill: color });
    const len = Math.hypot(b[0] - a[0], b[1] - a[1]) || 1, ux = (b[0] - a[0]) / len, uy = (b[1] - a[1]) / len, off = 0.28;
    g.append(line, head);
    g.set = (p) => {
      const d = off + (len - off) * p, tip = [a[0] + ux * d, a[1] + uy * d], hl = Math.min(0.36, d - off), base = [tip[0] - ux * hl, tip[1] - uy * hl], w = hl * 0.62;
      line.setAttribute('x1', a[0] + ux * off); line.setAttribute('y1', a[1] + uy * off);
      line.setAttribute('x2', base[0]); line.setAttribute('y2', base[1]);
      head.setAttribute('points', `${tip[0]},${tip[1]} ${base[0] - uy * w},${base[1] + ux * w} ${base[0] + uy * w},${base[1] - ux * w}`);
      return tip;
    };
    g.set(1);
    return g;
  }

  // 圈：set(p) 画到一整圈的 p 成
  function ringEl(c, color) {
    const r = 0.43, len = 2 * Math.PI * r;
    const el = sv('circle', { cx: c[0], cy: c[1], r, fill: 'none', stroke: color, 'stroke-width': 0.08, opacity: 0.9, 'stroke-dasharray': len, transform: `rotate(-90 ${c[0]} ${c[1]})` });
    el.set = (p) => { el.setAttribute('stroke-dashoffset', len * (1 - p)); return c; };
    el.set(1);
    return el;
  }
  const markEl = (m, flip) => (m.draw === 'arrow' ? arrowEl(sqPt(m.from, flip), sqPt(m.to, flip), MARK_COLORS[m.color]) : ringEl(sqPt(m.square, flip), MARK_COLORS[m.color]));

  let markLayer = null, markState = null; // markState：棋盘上现在画的是哪一组 { id, flip, timer }
  const markedKeys = new Set();           // 放过动画的标注：再回到这个局面时直接显示
  const boardFlip = () => { const b = getBoardEl(); return !!b && b.classList.contains('flipped'); };
  const markLost = () => !markLayer || !markLayer.isConnected || markState.flip !== boardFlip();

  function clearMarks() {
    if (markState && markState.timer) clearInterval(markState.timer);
    markState = null;
    if (markLayer) markLayer.textContent = '';
  }

  // 让棋盘上显示这些标注（已经是这一批就不重画）。list 里每项 { m, anim }：anim = 用光标画出来，否则直接显示
  function setMarks(id, list) {
    const board = getBoardEl(), flip = boardFlip();
    if (markState && markState.id === id && !markLost()) return;
    clearMarks();
    if (!board) return;
    if (!markLayer || markLayer.parentNode !== board) {
      if (markLayer) markLayer.remove();
      markLayer = sv('svg', { class: 'cwp-marks', viewBox: '0 0 8 8', style: 'position:absolute;left:0;top:0;width:100%;height:100%;pointer-events:none;z-index:10;overflow:visible' });
      board.appendChild(markLayer);
    }
    markState = { id, flip, timer: null };
    const live = opts.markAnimate ? list.filter((x) => x.anim).map((x) => x.m) : [];
    list.filter((x) => !live.includes(x.m)).forEach((x) => markLayer.appendChild(markEl(x.m, flip)));
    if (live.length) playMarks(markLayer, live, flip, markState);
  }

  // 标注动画：棋盘上出现一个鼠标光标，移到起点，按住拖到终点，画出箭头；圈格子就是移过去点一下
  function playMarks(svg, list, flip, st) {
    const ease = (p) => p * p * (3 - 2 * p), K = 0.75;
    const tip = sv('path', { d: 'M0 0V.5L.13 .39 .22 .6 .3 .57 .21 .36H.37Z', fill: '#fff', stroke: '#111', 'stroke-width': 0.04, 'stroke-linejoin': 'round', transform: `scale(${K})` });
    const cursor = sv('g', { class: 'cwp-cursor' });
    cursor.append(tip);
    svg.appendChild(cursor);
    const put = (pt) => cursor.setAttribute('transform', `translate(${pt[0]} ${pt[1]})`);
    const segs = []; // 一段一段的动画：{ ms, start?, run(p), end? }
    let here = null;
    const travel = (to) => { // 光标移过去（第一次从右下方滑进来）
      const from = here || [Math.min(8.3, to[0] + 1.6), Math.min(8.3, to[1] + 1.6)];
      here = to;
      segs.push({ ms: 220, run: (p) => put([from[0] + (to[0] - from[0]) * ease(p), from[1] + (to[1] - from[1]) * ease(p)]) });
    };
    list.forEach((m) => {
      const el = markEl(m, flip), start = () => { el.set(0); svg.insertBefore(el, cursor); };
      if (m.draw === 'arrow') {
        travel(sqPt(m.from, flip));
        segs.push({ ms: 340, start, run: (p) => put(el.set(ease(p))) }); // 按住拖过去：线跟着光标变长
        here = sqPt(m.to, flip);
      } else {
        travel(sqPt(m.square, flip));
        segs.push({ ms: 280, start, run: (p) => { el.set(ease(p)); tip.setAttribute('transform', `scale(${K * (1 - 0.2 * Math.sin(Math.PI * Math.min(1, p * 2.5)))})`); } }); // 点一下：光标缩一下，圈画出来
      }
      segs.push({ ms: 90, run: () => {} });
    });
    segs.push({ ms: 380, run: (p) => cursor.setAttribute('opacity', 1 - p), end: () => cursor.remove() });
    let i = 0, t0 = performance.now(), begun = false;
    st.timer = setInterval(() => {
      const now = performance.now();
      while (i < segs.length) {
        const s = segs[i];
        if (!begun) { begun = true; if (s.start) s.start(); }
        const p = Math.min(1, (now - t0) / s.ms);
        s.run(p);
        if (p < 1) break;
        if (s.end) s.end();
        i++; t0 += s.ms; begun = false;
      }
      if (i >= segs.length) { clearInterval(st.timer); st.timer = null; }
    }, 16);
  }

  // 现在棋盘上该标什么：
  //   · 你上一步的讲解还显示着：这段讲解里调用过的标注工具（讲到什么就标什么）。对手走了之后也留着，直到你走下一步
  //   · 轮到你走：再加上对方现在的威胁（红箭头；能吃到子就把那个子也圈出来）
  function updateMarks(me, pair) {
    if (!opts.marks) { clearMarks(); return; }
    const groups = []; // 准备好了的各组标注 { id, list }
    if (pair && curComp && !curComp.live) {
      groups.push({ id: curComp.key + (opts.markBetter ? '' : '|nobetter'), list: (curComp.tools || []).map((t) => t.result).filter((r) => r && r.draw && (opts.markBetter || r.note !== 'better')) });
    }
    if (opts.markThreats && cur && cur.done && !cur.error && !cur.over && cur.turn === me) {
      const nf = nullFen(cur.fen), ne = nf ? evalOf(nf) : null;
      if (ne && ne.done) {
        const t = threatOf(ne, cur, other(me)), log = [];
        if (t) {
          callTool('board_arrow', { from: t.m.from, to: t.m.to, color: 'red', note: 'threat' }, log);
          if (t.m.cap) callTool('board_circle', { square: t.m.to, color: 'red', note: 'attacked' }, log);
        }
        groups.push({ id: 'threat:' + cur.fen, list: log.map((x) => x.result).filter(Boolean) });
      }
    }
    const list = [], had = new Set();
    groups.forEach((g) => {
      const anim = !markedKeys.has(g.id); // 每组只在第一次出现时放动画，之后直接显示
      markedKeys.add(g.id);
      g.list.forEach((m) => {
        const k = m.draw + (m.from || m.square) + (m.to || '') + m.color;
        if (!had.has(k) && list.length < 10) { had.add(k); list.push({ m, anim }); } // 重复的不画第二遍；最多 10 个，免得太乱
      });
    });
    if (!list.length) { clearMarks(); return; }
    setMarks(groups.map((g) => g.id).join('||'), list);
  }

  // =====================================================================
  // 四人象棋（组队 Teams）：新增的独立模块，普通象棋那套逻辑完全不动。
  // 页面上出现四人棋盘时自动切到这里；只在分析棋盘里给评估和讲解（对局中不提供，FFA 暂不支持）。
  // 引擎：Titan（github.com/obryanlouis/4pchess，MIT 许可），编译成 WebAssembly，内置在脚本末尾的 TITAN4P_B64。
  // =====================================================================
  const C4 = ['R', 'B', 'Y', 'G'];                      // 走棋顺序：红 → 蓝 → 黄 → 绿（顺时针）
  const TEAM4 = { R: 0, Y: 0, B: 1, G: 1 };             // 红黄一队，蓝绿一队；引擎的评估分是红黄队视角
  const FILES4 = 'abcdefghijklmn';
  const VAL4 = { P: 1, N: 3, B: 4, R: 5, Q: 9, K: 0 };  // 讲解里说子力时用（按引擎分值折算成“兵”）
  // chess.com 棋子的 data-color 编号 → 颜色（需要用真实的四人对局页面确认）
  const COLOR_CODE4 = { 0: 'R', 1: 'B', 2: 'Y', 3: 'G', r: 'R', b: 'B', y: 'Y', g: 'G', red: 'R', blue: 'B', yellow: 'Y', green: 'G' };
  const START4 = 'x,x,x,yR,yN,yB,yK,yQ,yB,yN,yR,x,x,x/x,x,x,yP,yP,yP,yP,yP,yP,yP,yP,x,x,x/x,x,x,8,x,x,x/bR,bP,10,gP,gR/bN,bP,10,gP,gN/bB,bP,10,gP,gB/bQ,bP,10,gP,gK/bK,bP,10,gP,gQ/bB,bP,10,gP,gB/bN,bP,10,gP,gN/bR,bP,10,gP,gR/x,x,x,8,x,x,x/x,x,x,rP,rP,rP,rP,rP,rP,rP,rP,x,x,x/x,x,x,rR,rN,rB,rQ,rK,rB,rN,rR,x,x,x';
  // 王车易位的初始位置：[王, 短易位的车, 长易位的车]
  const CASTLE4 = { R: ['h1', 'k1', 'd1'], B: ['a7', 'a4', 'a11'], Y: ['g14', 'd14', 'k14'], G: ['n8', 'n11', 'n4'] };
  const N4 = [[1, 2], [2, 1], [-1, 2], [-2, 1], [1, -2], [2, -1], [-1, -2], [-2, -1]];
  const RK4 = [[1, 0], [-1, 0], [0, 1], [0, -1]], BS4 = [[1, 1], [1, -1], [-1, 1], [-1, -1]];
  const PDIR4 = { R: [0, -1], Y: [0, 1], B: [1, 0], G: [-1, 0] };   // 兵的前进方向

  const valid4 = (c, r) => c >= 0 && c < 14 && r >= 0 && r < 14 && !((c < 3 || c > 10) && (r < 3 || r > 10));
  const sq4 = (c, r) => FILES4[c] + (14 - r);   // r = 0 是最上面一行（黄方底线）
  const xy4 = (s) => [FILES4.indexOf(s[0]), 14 - +s.slice(1)];
  const pc4 = (p) => ({ c: p[0].toUpperCase(), t: p[1] }); // 'rP' → { c: 'R', t: 'P' }
  const enemy4 = (a, b) => TEAM4[a] !== TEAM4[b];

  function parseFen4(placement) {
    const b = {};
    placement.split('/').forEach((row, r) => {
      let c = 0;
      for (const tok of row.split(',')) {
        if (tok === 'x') c++;
        else if (/^\d+$/.test(tok)) c += +tok;
        else { b[sq4(c, r)] = tok; c++; }
      }
    });
    return b;
  }
  const START4_BOARD = parseFen4(START4);
  const boardKey4 = (b) => Object.keys(b).sort().map((s) => s + b[s]).join(' ');
  const START4_KEY = boardKey4(START4_BOARD);

  function fen4(b, turn) {
    const rows = [];
    for (let r = 0; r < 14; r++) {
      const cells = [];
      let e = 0;
      for (let c = 0; c < 14; c++) {
        const p = valid4(c, r) ? b[sq4(c, r)] : 'x';
        if (!p) { e++; continue; }
        if (e) { cells.push(String(e)); e = 0; }
        cells.push(p);
      }
      if (e) cells.push(String(e));
      rows.push(cells.join(','));
    }
    // 易位权：王和车都还在初始位置就算有
    const cr = (i) => C4.map((c) => (b[CASTLE4[c][0]] === c.toLowerCase() + 'K' && b[CASTLE4[c][i]] === c.toLowerCase() + 'R' ? 1 : 0)).join(',');
    return `${turn}-0,0,0,0-${cr(1)}-${cr(2)}-0,0,0,0-0-${rows.join('/')}`;
  }

  // sq 上的子攻击的格子（四个方向的兵、马、王、远程子）
  function attacks4(b, s) {
    const p = b[s];
    if (!p) return [];
    const { c, t } = pc4(p), [x, y] = xy4(s), out = [];
    const add = (X, Y) => { if (valid4(X, Y)) out.push(sq4(X, Y)); };
    if (t === 'P') {
      const [dx, dy] = PDIR4[c];
      if (dx) { add(x + dx, y - 1); add(x + dx, y + 1); } else { add(x - 1, y + dy); add(x + 1, y + dy); }
    } else if (t === 'N') N4.forEach(([dx, dy]) => add(x + dx, y + dy));
    else if (t === 'K') RK4.concat(BS4).forEach(([dx, dy]) => add(x + dx, y + dy));
    else {
      for (const [dx, dy] of t === 'R' ? RK4 : t === 'B' ? BS4 : RK4.concat(BS4)) {
        for (let i = 1; i < 14; i++) {
          const X = x + dx * i, Y = y + dy * i;
          if (!valid4(X, Y)) break;
          const s2 = sq4(X, Y);
          out.push(s2);
          if (b[s2]) break;
        }
      }
    }
    return out;
  }
  const attackers4 = (b, target, who) => Object.keys(b).filter((s) => s !== target && who(pc4(b[s]).c) && attacks4(b, s).includes(target));

  function parseMove4(str) {
    const m = /^([a-n]\d{1,2})-([a-n]\d{1,2})(?:=([NBRQ]))?/.exec(str || '');
    return m ? { from: m[1], to: m[2], promo: m[3] || null } : null;
  }
  const same4 = (str, mv) => { const m = parseMove4(str); return !!m && m.from === mv.from && m.to === mv.to; };

  function apply4(b, mv) {
    const n = { ...b }, p = n[mv.from];
    if (!p) return n;
    const [fx, fy] = xy4(mv.from), [tx, ty] = xy4(mv.to);
    if (p[1] === 'K' && Math.max(Math.abs(tx - fx), Math.abs(ty - fy)) === 2 && (tx === fx || ty === fy)) {
      // 易位：沿同一方向找到自己的车，跳到王的另一侧
      const dx = Math.sign(tx - fx), dy = Math.sign(ty - fy);
      for (let i = 1; i < 14; i++) {
        const X = fx + dx * i, Y = fy + dy * i;
        if (!valid4(X, Y)) break;
        const s2 = sq4(X, Y);
        if (n[s2] === p[0] + 'R') { n[sq4(fx + dx, fy + dy)] = n[s2]; delete n[s2]; break; }
        if (n[s2] && s2 !== mv.to) break;
      }
    }
    delete n[mv.from];
    n[mv.to] = mv.promo ? p[0] + mv.promo : p;
    return n;
  }

  function moveInfo4(b, mv) {
    if (!mv || !b[mv.from]) return null;
    const { c, t } = pc4(b[mv.from]), a = apply4(b, mv);
    const [fx, fy] = xy4(mv.from), [tx, ty] = xy4(mv.to);
    const kingSq = (col) => Object.keys(a).find((s) => a[s] === col.toLowerCase() + 'K');
    const checks = C4.filter((e) => enemy4(c, e) && kingSq(e) && attackers4(a, kingSq(e), (x) => x === c).length > 0);
    return {
      ...mv, color: c, piece: t, cap: b[mv.to] ? pc4(b[mv.to]) : null, checks, after: a,
      castle: t === 'K' && Math.max(Math.abs(tx - fx), Math.abs(ty - fy)) === 2 && (tx === fx || ty === fy),
    };
  }

  // 对比两个局面，还原刚走的那步
  function diffMove4(a, b) {
    const from = [], to = [];
    for (const s of new Set([...Object.keys(a), ...Object.keys(b)])) {
      if (a[s] === b[s]) continue;
      if (a[s] && !b[s]) from.push(s);
      else if (b[s]) to.push(s);
    }
    if (!to.length || to.length > 2) return null;
    const mover = pc4(b[to[0]]).c;
    if (to.some((s) => pc4(b[s]).c !== mover)) return null;
    const mf = from.filter((s) => pc4(a[s]).c === mover);
    if (!mf.length || mf.length !== to.length) return null;
    let f = mf[0], t = to[0];
    if (mf.length === 2) { // 易位
      f = mf.find((s) => a[s][1] === 'K');
      t = to.find((s) => b[s][1] === 'K');
      if (!f || !t) return null;
    }
    return { from: f, to: t, promo: a[f][1] === 'P' && b[t][1] !== 'P' ? b[t][1] : null, mover };
  }

  // 下一个走棋的一方（跳过已经没有王的一方）
  function nextTurn4(mover, b) {
    const alive = new Set(Object.values(b).filter((p) => p[1] === 'K').map((p) => p[0].toUpperCase()));
    for (let k = 1; k <= 4; k++) {
      const c = C4[(C4.indexOf(mover) + k) % 4];
      if (alive.has(c)) return c;
    }
    return mover;
  }

  // ---------- 读取页面上的四人棋盘 ----------
  // 按棋盘结构判断，不看网址：棋子有 3 种以上颜色，或者格子数超过 64（14×14 去掉四角是 160 格）
  const pieceEls4 = (root) => [...root.querySelectorAll('[data-piece][data-color]')];
  function fourWrap() {
    const known = document.querySelector('.container-four-board-wrapper');
    if (known) return known;
    // chess.com 改了类名也能找到：取所有棋子共同的最近容器
    const pcs = pieceEls4(document);
    if (new Set(pcs.map((p) => p.dataset.color)).size < 3) return null;
    let box = pcs[0].parentElement;
    while (box && !pcs.every((p) => box.contains(p))) box = box.parentElement;
    return box;
  }
  function isFour() {
    const w = fourWrap();
    if (!w) return false;
    return new Set(pieceEls4(w).map((p) => p.dataset.color)).size >= 3 || w.querySelectorAll('.square').length > 64;
  }

  function readBoard4() {
    const w = fourWrap();
    if (!w) return null;
    const box = (w.querySelector('.TheBoard-squares') || w).getBoundingClientRect(), size = box.width / 14;
    const raw = [];
    pieceEls4(w).forEach((el) => {
      const color = COLOR_CODE4[String(el.dataset.color).toLowerCase()];
      const t = String(el.dataset.piece || '').toUpperCase();
      const m = /translate\((-?[\d.]+)px,\s*(-?[\d.]+)px\)/.exec(el.getAttribute('style') || '');
      if (color && 'PNBRQK'.includes(t) && t && m) raw.push({ color, t, sc: Math.round(+m[1] / size), sr: Math.round(+m[2] / size) });
    });
    if (raw.length < 4) return null;
    // 棋盘可能被旋转（你执蓝/黄/绿时自己在下面）：选出最符合“红在下、黄在上、蓝在左、绿在右”的旋转
    const ROT = [(c, r) => [c, r], (c, r) => [13 - r, c], (c, r) => [13 - c, 13 - r], (c, r) => [r, 13 - c]];
    const avg = (a, i) => (a.length ? a.reduce((s, v) => s + v[i], 0) / a.length : 6.5);
    let best = 0, bestScore = -Infinity;
    ROT.forEach((f, k) => {
      const g = { R: [], Y: [], B: [], G: [] };
      raw.forEach((p) => g[p.color].push(f(p.sc, p.sr)));
      const score = avg(g.R, 1) - avg(g.Y, 1) + avg(g.G, 0) - avg(g.B, 0);
      if (score > bestScore) { bestScore = score; best = k; }
    });
    const board = {};
    raw.forEach((p) => { const [c, r] = ROT[best](p.sc, p.sr); if (valid4(c, r)) board[sq4(c, r)] = p.color.toLowerCase() + p.t; });
    // 屏幕最下面的一方就是“你”
    const byColor = {};
    raw.forEach((p) => (byColor[p.color] = byColor[p.color] || []).push([p.sc, p.sr]));
    const me = Object.keys(byColor).sort((a, b) => avg(byColor[b], 1) - avg(byColor[a], 1))[0];
    return { board, me, key: boardKey4(board) };
  }

  // FFA（各自为战）暂不支持（怎么判断 FFA，需要用真实的四人对局页面确认）
  function state4() {
    const area = (fourWrap() && fourWrap().closest('main')) || document.body;
    if (/\b(FFA|Free[- ]for[- ]All)\b|自由混战|各自为战/i.test(area.innerText) && !/\bTeams?\b|组队|团队/i.test(area.innerText)) return 'ffa';
    return 'ok';
  }

  // ---------- 四人引擎（Web Worker 里跑 WebAssembly 版 Titan） ----------
  const ev4 = new Map(); // FEN → { done, cp（红黄队视角）, mate, depth, best, pv, error }
  const q4 = [];
  let w4 = null, w4Ready = false, w4Busy = null, w4Failed = false;

  function start4() {
    if (w4 || w4Failed) return;
    try {
      const bytes = Uint8Array.from(atob(TITAN4P_B64), (ch) => ch.charCodeAt(0));
      const glue = `\n;Titan4P().then((M) => {\n  self.onmessage = (e) => self.postMessage({ out: M.ccall('analyze', 'string', ['string', 'number', 'number'], [e.data.fen, e.data.ms, 40]) });\n  self.postMessage({ ready: true });\n});\n`;
      w4 = new Worker(URL.createObjectURL(new Blob([bytes, glue], { type: 'text/javascript' })));
      w4.onmessage = (ev) => {
        if (ev.data.ready) { w4Ready = true; pump4(); render(); return; }
        const e = w4Busy;
        w4Busy = null;
        if (e) {
          let d = {};
          try { d = JSON.parse(ev.data.out); } catch (err) { /* 引擎输出异常 */ }
          if (d.ok) {
            const pv = d.pv && d.pv[0] === d.best ? d.pv : [d.best]; // 最后一层没搜完时变化可能对不上最佳着法
            Object.assign(e, { cp: d.score, mate: !!d.mate, depth: d.depth, best: d.best, pv });
          } else e.error = d.error || 'engine';
          e.done = true;
        }
        render();
        pump4();
      };
      w4.onerror = () => { w4Failed = true; render(); };
    } catch (err) {
      w4Failed = true;
    }
  }
  function pump4() {
    start4();
    if (!w4Ready || w4Busy || !q4.length) return;
    w4Busy = q4.shift();
    w4.postMessage({ fen: w4Busy.fen, ms: 1500 });
  }
  function eval4(fen, urgent) {
    let e = ev4.get(fen);
    if (!e) { e = { fen, done: false }; ev4.set(fen, e); q4.push(e); }
    if (urgent && q4.indexOf(e) > 0) { q4.splice(q4.indexOf(e), 1); q4.unshift(e); }
    pump4();
    return e;
  }

  // ---------- 四人模式的局面跟踪 ----------
  let cur4 = null, prev4 = null, last4 = null, pair4 = null, me4 = null, state4Last = null;

  function tick4() {
    const st = state4();
    if (st !== state4Last) { state4Last = st; render(); }
    if (st !== 'ok') return;
    const snap = readBoard4();
    if (!snap || (cur4 && snap.key === cur4.key)) return;
    me4 = snap.me;
    const mv = cur4 ? diffMove4(cur4.board, snap.board) : null;
    let turn = null;
    if (mv && cur4.turn && mv.mover === cur4.turn) turn = nextTurn4(mv.mover, snap.board);
    else if (snap.key === START4_KEY) turn = 'R';
    else if (mv) turn = nextTurn4(mv.mover, snap.board); // 中途接手：按刚走的一方推算
    const next = { key: snap.key, board: snap.board, turn, fen: turn ? fen4(snap.board, turn) : null };
    last4 = mv && cur4 && cur4.turn === mv.mover ? mv : null;
    if (!last4) pair4 = null;                            // 来回跳转：旧讲解作废
    else if (mv.mover === me4) pair4 = { prev: cur4, cur: next, move: mv };
    prev4 = cur4;
    cur4 = next;
    if (next.fen) eval4(next.fen, true);
    render();
  }

  // ---------- 讲解素材 ----------
  function buildCtx4(pair) {
    const { prev: before, cur: after, move } = pair, me = move.mover, team = TEAM4[me];
    const e0 = ev4.get(before.fen), e1 = ev4.get(after.fen);
    const winT = (e) => {
      if (e.mate) return (e.cp > 0) === (team === 0) ? 100 : 0;
      const cp = team === 0 ? e.cp : -e.cp;
      return 50 + 50 * (2 / (1 + Math.exp(-0.00368208 * cp)) - 1);
    };
    const cpT = (e) => (e.mate || e.cp == null ? null : (team === 0 ? e.cp : -e.cp) / 100);
    const played = moveInfo4(before.board, move);
    const delivered = e1.error === 'no move' && played.checks.length > 0; // 走完对方已无棋可走：将死
    const wb = winT(e0), wa = delivered ? 100 : e1.error ? wb : winT(e1), loss = Math.max(0, wb - wa);
    const isBest = !!e0.best && same4(e0.best, move);
    const best = !isBest && e0.best ? moveInfo4(before.board, parseMove4(e0.best)) : null;
    const reply = e1.pv && e1.pv[0] ? moveInfo4(after.board, parseMove4(e1.pv[0])) : null;
    // 对手的最佳应对吃掉我方（包括队友）的子，下一步也吃不回来：送子
    let freeLoss = 0;
    if (reply && reply.cap && TEAM4[reply.cap.c] === team) {
      const re = e1.pv[1] ? moveInfo4(reply.after, parseMove4(e1.pv[1])) : null;
      freeLoss = VAL4[reply.cap.t] - (re && re.to === reply.to && re.cap ? VAL4[re.cap.t] : 0);
    }
    const myMate = (e) => !!e && e.mate && (e.cp > 0) === (team === 0);
    const oppMate = (e) => !!e && e.mate && (e.cp > 0) !== (team === 0);
    let kind;
    if (delivered) kind = 'mate';
    else if (myMate(e0) && !myMate(e1)) kind = 'missedMate';
    else if (myMate(e1)) kind = 'mating';
    else if (isBest) kind = 'best';
    else if (loss < 2) kind = 'excellent';
    else if (loss < 5) kind = 'good';
    else if (loss < 10) kind = 'inaccuracy';
    else if (loss < 20) kind = 'mistake';
    else kind = 'blunder';
    // 这步的子在攻击对手值钱或没保护的子（自己不悬着时才算）
    let threat = null;
    const safe = !(reply && reply.cap && reply.to === played.to);
    if (safe && !played.castle) {
      for (const s of attacks4(played.after, played.to)) {
        const p = played.after[s];
        if (!p) continue;
        const o = pc4(p);
        if (!enemy4(me, o.c) || o.t === 'K' || o.t === 'P') continue;
        const guarded = attackers4(played.after, s, (x) => !enemy4(x, o.c)).length > 0;
        if ((VAL4[o.t] > VAL4[played.piece] || !guarded) && (!threat || VAL4[o.t] > VAL4[threat.t])) threat = o;
      }
    }
    return {
      me, team, kind, played, best, reply, wb, wa, loss, threat,
      cpB: cpT(e0), cpA: delivered || e1.error ? null : cpT(e1),
      phase: 'middlegame', stBefore: stateOf(wb), stAfter: stateOf(wa),
      hanging: freeLoss - (reply && reply.to === played.to && played.cap ? VAL4[played.cap.t] : 0) >= 2,
      sacrifice: !!reply && reply.to === played.to && freeLoss - (played.cap ? VAL4[played.cap.t] : 0) >= 2 && loss < 5,
      oppMateAfter: oppMate(e1) ? 1 : null, mateAfter: myMate(e1) ? 1 : null, mateBefore: null,
      tags: [], oppThreat: null, myThreat: null, parried: false,
      seed: before.fen + move.from + move.to,
    };
  }

  // ---------- 四人讲解：一段连贯的口语，和普通象棋共用选词网络 ----------
  function compose4(c, W, S) {
    const P = W.PN4, CN = W.CN4, bad = BAD.includes(c.kind), mine = (col, t) => (col === c.me ? W.yours4(P[t]) : W.mate4(CN[col], P[t]));
    const talk = makeTalk(W, S), say = talk.say;
    say('heads.' + c.kind, {});
    if (['mistake', 'blunder'].includes(c.kind) && c.cpB != null && c.cpA != null && c.cpB - c.cpA >= 0.3) say('evalDrop', { d: (c.cpB - c.cpA).toFixed(1) });

    const rs = [], p = c.played;
    if (p.castle) rs.push({ type: 'castle', key: 'castle', mag: 0.3 });
    if (p.promo) rs.push({ type: 'promo', key: 'promo', p: { x: P[p.promo] }, mag: 1 });
    if (p.cap) rs.push({ type: 'freeCapture', key: 'cap4', p: { who: CN[p.cap.c], x: P[p.cap.t] }, mag: VAL4[p.cap.t] / 9 });
    if (p.checks.length >= 2) rs.push({ type: 'fork', key: 'doubleCheck4', p: { who: W.list(p.checks.map((x) => CN[x])) }, mag: 1 });
    else if (p.checks.length && c.kind !== 'mate') rs.push({ type: 'check', key: 'check4', p: { who: CN[p.checks[0]] }, mag: 0.4 });
    if (c.threat) rs.push({ type: 'threat', key: 'threat4', p: { piece: P[p.piece], who: CN[c.threat.c], x: P[c.threat.t] }, mag: VAL4[c.threat.t] / 9 });
    if (c.sacrifice) rs.push({ type: 'sacrifice', key: 'sacrifice', p: { x: P[c.reply.cap.t] }, mag: 0.5 });
    const chosen = rs.length && c.kind !== 'mate' ? S.select(rs, 1, 0, W) : [];
    chosen.forEach((r, i) => { say(i === 0 ? (bad || c.kind === 'good' ? 'join.badIdea' : 'join.idea') : 'join.more'); say(r.key, r.p); });
    if (!chosen.length && !bad && c.kind !== 'good' && c.kind !== 'mate') { say('join.idea'); say('quiet', { piece: P[p.piece] }); }

    if (bad && (c.oppMateAfter || c.hanging || c.reply)) {
      say('join.problem');
      if (c.oppMateAfter) say('mated4', { team: W.TEAMS4[1 - c.team] });
      else if (c.hanging) say('hanging4', { who: CN[c.reply.color], m: W.move4(c.reply), x: mine(c.reply.cap.c, c.reply.cap.t) });
      else say(c.reply.checks.includes(c.me) ? 'replyCheck4' : 'reply4', { who: CN[c.reply.color], m: W.move4(c.reply) });
    }

    if (c.best && (bad || c.kind === 'good')) {
      const why = [];
      if (c.best.cap) { const q = { who: CN[c.best.cap.c], x: P[c.best.cap.t] }; why.push(async () => (await S.gen('reason4.cap', q)) || W.reason4.cap(q)); }
      if (c.best.checks.length) { const q = { who: W.list(c.best.checks.map((x) => CN[x])) }; why.push(async () => (await S.gen('reason4.check', q)) || W.reason4.check(q)); }
      say('join.better');
      talk.add(W.move4(c.best));
      if (why.length) { say('join.why'); talk.later(why[0]); }
    }

    if (['mistake', 'blunder', 'missedMate'].includes(c.kind)) { say('join.tip'); say(c.hanging ? 'tipHanging' : 'tips4'); }
    return talk.done().then((text) => [{ text }]);
  }

  const compCache4 = new Map();
  function composeCached4(c) {
    return composeVia(compCache4, c.seed + '|4p', c, true, (S) => compose4(c, W4_EN, S));
  }

  // ---------- 四人模式的面板 ----------
  const TEAM_BG4 = ['linear-gradient(90deg,#d0463f,#e3b21f)', 'linear-gradient(90deg,#3b7dd8,#3fa45b)'];

  function render4(T) {
    const F = T.four;
    $('.side').style.display = 'none';
    const st = state4();
    let evText = '—', sub = '', w = 50, stLine = w4Failed ? F.engineFail : w4Ready ? F.engine : F.engineLoading;
    const team = me4 ? TEAM4[me4] : 0;
    let cls = '#666', title = F.title, paras, change = '';
    curComp = null;

    if (st === 'ffa') { sub = F.ffaShort; paras = [{ text: F.ffa }]; stLine = ''; }
    else {
      const e = cur4 && cur4.fen ? ev4.get(cur4.fen) : null;
      if (!cur4 || !cur4.turn) sub = F.turnUnknown;
      else if (!e || !e.done) sub = F.thinking;
      else if (e.error) sub = e.error === 'no move' ? F.gameOver : F.noEval;
      else {
        const cp = team === 0 ? e.cp : -e.cp;
        w = e.mate ? (cp > 0 ? 100 : 0) : 50 + 50 * (2 / (1 + Math.exp(-0.00368208 * cp)) - 1);
        evText = e.mate ? (cp > 0 ? '+M' : '-M') : (cp > 0 ? '+' : '') + (cp / 100).toFixed(1);
        const tn = F.teams[team];
        sub = (Math.abs(cp) < 30 && !e.mate ? F.even : cp > 0 ? F.lead(tn) : F.behind(tn)) + T.depth(e.depth);
      }
      // 讲解：只讲你（屏幕下方那一方）自己的棋
      if (!pair4) { title = T.promptT; paras = [{ text: T.prompt }]; }
      else {
        const e0 = ev4.get(pair4.prev.fen), e1 = ev4.get(pair4.cur.fen);
        if (!e0 || !e1 || !e0.done || !e1.done) { title = T.thinkingT; paras = [{ text: T.thinking }]; }
        else if (e0.error) { title = T.noEvalT; paras = [{ text: T.noEval }]; }
        else {
          const c = buildCtx4(pair4);
          cls = COLORS[c.kind];
          title = T.labels[c.kind];
          curComp = composeCached4(c);
          paras = curComp ? curComp.paras : [{ text: '▍' }];
          change = T.change(pct(c.wb), pct(c.wa));
        }
      }
    }

    const ev = $('.ev');
    ev.textContent = evText;
    ev.style.color = w > 55 ? '#f0f0f0' : w < 45 ? '#9e9b98' : '#e8e6e3';
    $('.sub').textContent = sub;
    $('.st').textContent = stLine;
    $('.bar').style.background = TEAM_BG4[1 - team];
    $('.bar .w').style.background = TEAM_BG4[team];
    $('.bar .w').style.width = w.toFixed(1) + '%';
    $('.lw').textContent = F.teamsShort[team] + ' ' + pct(w);
    $('.lb').textContent = pct(100 - w) + ' ' + F.teamsShort[1 - team];
    $('.lw').style.color = $('.lb').style.color = '#fff';
    const W = W4_EN;
    $('.nt').textContent = last4 && me4 && last4.mover !== me4 && prev4 ? F.moved(W.CN4[last4.mover], W.move4(moveInfo4(prev4.board, last4) || { piece: 'P', to: last4.to })) : '';
    renderComment(T, cls, title, paras, change);
  }

  // ---------- 四人讲解用语（在普通象棋的口语措辞上补充四人专用的） ----------
  const PN4_EN = { P: 'pawn', N: 'knight', B: 'bishop', R: 'rook', Q: 'queen', K: 'king' };
  const W4_EN = {
    ...W_EN,
    PN4: PN4_EN,
    CN4: { R: 'Red', B: 'Blue', Y: 'Yellow', G: 'Green' },
    TEAMS4: ['Red-Yellow', 'Blue-Green'],
    move4: (m) => `${PN4_EN[m.piece]} ${m.cap ? 'takes' : 'to'} ${m.to}${m.promo ? ` promoting to a ${PN4_EN[m.promo]}` : ''}`,
    yours4: (x) => `your ${x}`,
    mate4: (who, x) => `your teammate ${who}'s ${x}`,
    heads: { ...W_EN.heads, missedMate: ['So close, you had a mate and let it slip', 'You missed a chance to deliver mate'], mating: ["You've locked in the win, mate is coming", "It's a forced mate, the win is right there"] },
    cap4: [(p) => `you capture ${p.who}'s ${p.x}`, (p) => `you pick up ${p.who}'s ${p.x}`],
    check4: [(p) => `you check ${p.who}, who has to respond first`, (p) => `you give ${p.who} a check`],
    doubleCheck4: [(p) => `you check ${p.who} at the same time, so both have to respond`],
    threat4: [(p) => `your ${p.piece} attacks ${p.who}'s ${p.x} and puts them on the defensive`, (p) => `your ${p.piece} targets ${p.who}'s ${p.x}`],
    mated4: [(p) => `after this, ${p.team} have a mating attack`],
    hanging4: [(p) => `${p.who} can play ${p.m} and win ${p.x} for free`, (p) => `${p.x} is left unprotected, and ${p.who} can take it with ${p.m}`],
    reply4: [(p) => `you need to watch out for ${p.who}'s ${p.m}`, (p) => `${p.who}'s best reply is ${p.m}`],
    replyCheck4: [(p) => `${p.who} can reply ${p.m}, giving you check`, (p) => `next, ${p.who} has ${p.m} with check`],
    reason4: { cap: (p) => `it wins ${p.who}'s ${p.x}`, check: (p) => `it checks ${p.who}` },
    tips4: ['in four-player chess, watch both opponents, not just one side', 'keep your own pieces safe first, then coordinate with your teammate', "before each move, check whether either opponent can take something next"],
  };

  // ---------- 主循环：局面变了就去查询 ----------
  function tick() {
    const shown = onPage();
    if (panel.style.display !== (shown ? '' : 'none')) {
      panel.style.display = shown ? '' : 'none';
      if (!shown) stopSpeak();
    }
    if (!shown) return;
    if (isFour()) { tick4(); return; } // 四人象棋：交给四人模块
    const r = readFen();
    if (markState && markLost()) render(); // 棋盘翻转了、或者标注层被页面清掉了：重画
    if (!r || (cur && r.fen === cur.fen)) return;

    const next = evalOf(r.fen); // 已查过的局面直接用缓存
    const qi = sfQueue.indexOf(next);
    if (qi > 0) { sfQueue.splice(qi, 1); sfQueue.unshift(next); } // 本地排队时优先算当前局面
    lastMove = null;
    if (cur) {
      const mv = diffMove(cur.fen, next.fen);
      const oneStep = !r.exact || plyOf(next.fen) === plyOf(cur.fen) + 1;
      if (mv && oneStep && mv.mover === cur.turn) lastMove = mv; // 只讲解“往前走一步”
      else pairs = {}; // 来回跳转：旧讲解作废
    }
    prev = cur;
    cur = next;
    if (lastMove) pairs[lastMove.mover] = { prev, cur, move: lastMove };
    render();
  }

  // Titan 四人象棋引擎（github.com/obryanlouis/4pchess，MIT 许可，Copyright (c) 2023 obryanlouis），
  // 用 Emscripten 编译成的 WebAssembly 单文件（源码与补丁见 engine4p/），这里是它原始字节的 base64
  const TITAN4P_B64 = 'dmFyIFRpdGFuNFA9KCgpPT57dmFyIF9zY3JpcHROYW1lPWdsb2JhbFRoaXMuZG9jdW1lbnQ/LmN1cnJlbnRTY3JpcHQ/LnNyYztyZXR1cm4gYXN5bmMgZnVuY3Rpb24obW9kdWxlQXJnPXt9KXt2YXIgTW9kdWxlPW1vZHVsZUFyZzt2YXIgRU5WSVJPTk1FTlRfSVNfV0VCPSEhZ2xvYmFsVGhpcy53aW5kb3c7dmFyIEVOVklST05NRU5UX0lTX1dPUktFUj0hIWdsb2JhbFRoaXMuV29ya2VyR2xvYmFsU2NvcGU7dmFyIEVOVklST05NRU5UX0lTX05PREU9Z2xvYmFsVGhpcy5wcm9jZXNzPy52ZXJzaW9ucz8ubm9kZSYmZ2xvYmFsVGhpcy5wcm9jZXNzPy50eXBlIT0icmVuZGVyZXIiO3ZhciBwcm9ncmFtQXJncz1bXTt2YXIgdGhpc1Byb2dyYW09Ii4vdGhpcy5wcm9ncmFtIjt2YXIgcXVpdF89KHN0YXR1cyx0b1Rocm93KT0+e3Rocm93IHRvVGhyb3d9O2lmKHR5cGVvZiBfX2ZpbGVuYW1lIT0idW5kZWZpbmVkIil7X3NjcmlwdE5hbWU9X19maWxlbmFtZX1lbHNlIGlmKEVOVklST05NRU5UX0lTX1dPUktFUil7X3NjcmlwdE5hbWU9c2VsZi5sb2NhdGlvbi5ocmVmfXZhciBzY3JpcHREaXJlY3Rvcnk9IiI7dmFyIHJlYWRBc3luYyxyZWFkQmluYXJ5O2lmKEVOVklST05NRU5UX0lTX05PREUpe3ZhciBmcz1yZXF1aXJlKCJub2RlOmZzIik7c2NyaXB0RGlyZWN0b3J5PV9fZGlybmFtZSsiLyI7cmVhZEJpbmFyeT1maWxlbmFtZT0+e2ZpbGVuYW1lPWlzRmlsZVVSSShmaWxlbmFtZSk/bmV3IFVSTChmaWxlbmFtZSk6ZmlsZW5hbWU7dmFyIHJldD1mcy5yZWFkRmlsZVN5bmMoZmlsZW5hbWUpO3JldHVybiByZXR9O3JlYWRBc3luYz1hc3luYyhmaWxlbmFtZSxiaW5hcnk9dHJ1ZSk9PntmaWxlbmFtZT1pc0ZpbGVVUkkoZmlsZW5hbWUpP25ldyBVUkwoZmlsZW5hbWUpOmZpbGVuYW1lO3ZhciByZXQ9ZnMucmVhZEZpbGVTeW5jKGZpbGVuYW1lLGJpbmFyeT91bmRlZmluZWQ6InV0ZjgiKTtyZXR1cm4gcmV0fTtpZihwcm9jZXNzLmFyZ3YubGVuZ3RoPjEpe3RoaXNQcm9ncmFtPXByb2Nlc3MuYXJndlsxXS5yZXBsYWNlKC9cXC9nLCIvIil9cHJvZ3JhbUFyZ3M9cHJvY2Vzcy5hcmd2LnNsaWNlKDIpO3F1aXRfPShzdGF0dXMsdG9UaHJvdyk9Pntwcm9jZXNzLmV4aXRDb2RlPXN0YXR1czt0aHJvdyB0b1Rocm93fX1lbHNlIGlmKEVOVklST05NRU5UX0lTX1dFQnx8RU5WSVJPTk1FTlRfSVNfV09SS0VSKXt0cnl7c2NyaXB0RGlyZWN0b3J5PW5ldyBVUkwoIi4iLF9zY3JpcHROYW1lKS5ocmVmfWNhdGNoe317aWYoRU5WSVJPTk1FTlRfSVNfV09SS0VSKXtyZWFkQmluYXJ5PXVybD0+e3ZhciB4aHI9bmV3IFhNTEh0dHBSZXF1ZXN0O3hoci5vcGVuKCJHRVQiLHVybCxmYWxzZSk7eGhyLnJlc3BvbnNlVHlwZT0iYXJyYXlidWZmZXIiO3hoci5zZW5kKG51bGwpO3JldHVybiBuZXcgVWludDhBcnJheSh4aHIucmVzcG9uc2UpfX1yZWFkQXN5bmM9YXN5bmMgdXJsPT57dmFyIHJlc3BvbnNlPWF3YWl0IGZldGNoKHVybCx7Y3JlZGVudGlhbHM6InNhbWUtb3JpZ2luIn0pO2lmKHJlc3BvbnNlLm9rKXtyZXR1cm4gcmVzcG9uc2UuYXJyYXlCdWZmZXIoKX10aHJvdyBuZXcgRXJyb3IocmVzcG9uc2Uuc3RhdHVzKyIgOiAiK3Jlc3BvbnNlLnVybCl9fX1lbHNle312YXIgb3V0PWNvbnNvbGUubG9nLmJpbmQoY29uc29sZSk7dmFyIGVycj1jb25zb2xlLmVycm9yLmJpbmQoY29uc29sZSk7dmFyIHdhc21CaW5hcnk7dmFyIEFCT1JUPWZhbHNlO3ZhciBpc0ZpbGVVUkk9ZmlsZW5hbWU9PmZpbGVuYW1lLnN0YXJ0c1dpdGgoImZpbGU6Ly8iKTtjbGFzcyBFbXNjcmlwdGVuRUh7fWNsYXNzIEVtc2NyaXB0ZW5TakxqIGV4dGVuZHMgRW1zY3JpcHRlbkVIe31mdW5jdGlvbiBiaW5hcnlEZWNvZGUoYmluKXtmb3IodmFyIGk9MCxsPWJpbi5sZW5ndGgsbz1uZXcgVWludDhBcnJheShsKSxjO2k8bDsrK2kpe2M9YmluLmNoYXJDb2RlQXQoaSk7b1tpXT1+Yz4+OCZjfXJldHVybiBvfXZhciBydW50aW1lSW5pdGlhbGl6ZWQ9ZmFsc2U7ZnVuY3Rpb24gZ2V0TWVtb3J5QnVmZmVyKCl7cmV0dXJuIHdhc21NZW1vcnkuYnVmZmVyfWZ1bmN0aW9uIHVwZGF0ZU1lbW9yeVZpZXdzKCl7aWYoSEVBUDg/LmJ1ZmZlcj8ucmVzaXphYmxlKXJldHVybjt2YXIgYj1nZXRNZW1vcnlCdWZmZXIoKTtIRUFQOD1uZXcgSW50OEFycmF5KGIpO0hFQVBVOD1uZXcgVWludDhBcnJheShiKTtIRUFQMzI9bmV3IEludDMyQXJyYXkoYik7SEVBUFUzMj1uZXcgVWludDMyQXJyYXkoYik7SEVBUDY0PW5ldyBCaWdJbnQ2NEFycmF5KGIpfWZ1bmN0aW9uIHByZVJ1bigpe3ZhciBwcmVSdW49TW9kdWxlWyJwcmVSdW4iXTtpZihwcmVSdW4pe2lmKHR5cGVvZiBwcmVSdW49PSJmdW5jdGlvbiIpcHJlUnVuPVtwcmVSdW5dO29uUHJlUnVucy5wdXNoKC4uLnByZVJ1bil9Y2FsbFJ1bnRpbWVDYWxsYmFja3Mob25QcmVSdW5zKX1mdW5jdGlvbiBpbml0UnVudGltZSgpe3J1bnRpbWVJbml0aWFsaXplZD10cnVlO2lmKCFNb2R1bGVbIm5vRlNJbml0Il0mJiFGUy5pbml0aWFsaXplZClGUy5pbml0KCk7VFRZLmluaXQoKTt3YXNtRXhwb3J0c1sibCJdKCk7RlMuaWdub3JlUGVybWlzc2lvbnM9ZmFsc2V9ZnVuY3Rpb24gcG9zdFJ1bigpe3ZhciBwb3N0UnVuPU1vZHVsZVsicG9zdFJ1biJdO2lmKHBvc3RSdW4pe2lmKHR5cGVvZiBwb3N0UnVuPT0iZnVuY3Rpb24iKXBvc3RSdW49W3Bvc3RSdW5dO29uUG9zdFJ1bnMucHVzaCguLi5wb3N0UnVuKX1j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k8KdezYCHCABQcO/AToAGiABQQA7ABggAULDhMKJw6PCsMOAwpjChsOiRDcAECABQcKBw5PCnXs2AgwgAUHDvwE6AFxuIAFBADsACCABQsOEwonDo8Kww4DCmMKGw6JENwAAIANBIGoiA0HCgMOMOkdccgALIAI2AgBBwoDDgiUQCyECQQAhAwNAIAIgA2oiAUHCgcOTwp17NgIcIAFBw78BOgAaIAFBADsAGCABQsOEwonDo8Kww4DCmMKGw6JENwAQIAFBwoHDk8KdezYCDCABQcO/AToAXG4gAUEAOwAIIAFCw4TCicOjwrDDgMKYwobDokQ3AAAgA0EgaiIDQcKAw4IlR1xyAAsgACACNgLCgMOrUyAAQQgQCyIBNgLChMOrUyABQcKAwpHClwcQCzYCACABQcKAwpHClwcQCzYCBCAACxIAIAQgAjYCACAHIAU2AgBBAwsqAQF/IABBwowwNgIAAkAgACgCCCIBRVxyACAALQAMQQFxRVxyACABEFxuCyAACwQAIAELXCcBAX8gACgCACgCACgCAEHCmMKZAUHCmMKZASgCAEEBaiIBNgIAIAE2AgQLwrABAQR/IABBw7gvNgIAIABBCGohAwNAIAAoAgwgACgCCCIBa0ECdSACSwRAAkAgASACQQJ0aigCACIBRVxyACABIAEoAgQiBEEBazYCBCAEXHIAIAEgASgCACgCCBEBAAsgAkEBaiECDAELCyAAQcKQAWoQDBojAEEQayIBJAAgASADNgIMIAEoAgwiAigCACIDBEAgAiADNgIEIAIoAggaIAJBDGogAxDDgwELIAFBEGokACAACzoBAX9Bw7jClwEoAgAiASAAQQJ0aiEAA0AgACABRgRAQcO4wpcBIAA2AgAFIAFBADYCACABQQRqIQEMAQsLCx8AIABBw4g4NgIAIAAoAggQOkcEQCAAKAIIEMO8AQsgAAsEAEF/C2MBAX8jAEEgayICJAAgACwAC0EASARAIAJBADYCGCACQgA3AxAgAkIANwMAIAJBADYCCCAAIAIQTAsgACABKAIINgIIIAAgASkCADcCACABQQA6AAsgAUEANgIAIAJBIGokAAvCrQMBBX8CQAJAAkAgAQR/IAFBwoDCgMKAwoAET1xyASABQQJ0EAsFQQALIQMgACgCACECIAAgAzYCACACBEAgACgCBBogAhBc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AQsgA0EBR1xyASABQQE2AiAPCyABIAI2AhQgASADNgIgIAEgASgCKEEBajYCKAJAIAEoAiRBAUdccgAgASgCGEECR1xyACABQQE6ADYLIAFBBDYCLAsLwogCAAJAIAAgASgCCCAEEDEEQCACIAEoAgRHXHIBIAEoAhxBAUZccgEgASADNgIcDwsgACABKAIAIAQQMQRAAkAgASgCECACRwRAIAIgASgCFEdccgELIANBAUdccgIgAUEBNgIgDwsgASADNgIgAkAgASgCLEEERlxyACABQQA7ATQgACgCCCIAIAEgAiACQQEgBCAAKAIAKAIUEQwAIAEtADVBAUYEQCABQQM2AiwgAS0ANEVccgEMAwsgAUEENgIsCyABIAI2AhQgASABKAIoQQFqNgIoIAEoAiRBAUdccgEgASgCGEECR1xyASABQQE6ADYPCyAAKAIIIgAgASACIAMgBCAAKAIAKAIYEQsACwvCvQQBA38CQCAAIAEoAgggBBAxBEAgAiABKAIER1xyASABKAIcQQFGXHIBIAEgAzYCHA8LAkAgACABKAIAIAQQMQRAAkAgASgCECACRwRAIAIgASgCFEdccgELIANBAUdccgMgAUEBNgIgDwsgASADNgIgIAEoAixBBEZccgEgAEEQaiIFIAAoAgxBA3RqIQdBACEDA0ACQAJAIAECfwJAIAUgB09ccgAgAUEAOwE0IAUgASACIAJBASAEEMKAASABLQA2XHIAIAEtADVBAUdccgMgAS0ANEEBRgRAIAEoAhhBAUZccgNBASEGQQEhAyAALQAIQQJxRVxyAwwEC0EBIQMgAC0ACEEBcVxyA0EDDAELQQNBBCADGws2AiwgBlxyBQwECyABQQM2AiwMBAsgBUEIaiEFDAALAAsgACgCDCEFIABBEGoiBiABIAIgAyAEEGMgBUECSVxyASAGIAVBA3RqIQYgAEEYaiEFAkAgACgCCCIAQQJxRQRAIAEoAiRBAUdccgELA0AgAS0ANlxyAyAFIAEgAiADIAQQYyAFQQhqIgUgBklccgALDAILIABBAXFFBEADQCABLQA2XHIDIAEoAiRBAUZccgMgBSABIAIgAyAEEGMgBUEIaiIFIAZJXHIADAMLAAsDQCABLQA2XHICIAEoAiRBAUYEQCABKAIYQQFGXHIDCyAFIAEgAiADIAQQYyAFQQhqIgUgBklccgALDAELIAEgAjYCFCABIAEoAihBAWo2AiggASgCJEEBR1xyACABKAIYQQJHXHIAIAFBAToANgsLcgECfyAAKAIEIAEoAggoAgRGBEAgASACIAMQwoIBDwsgACgCDCEEIABBEGoiBSABIAIgAxDCuwECQCAEQQJJXHIAIAUgBEEDdGohBCAAQRhqIQADQCAAIAEgAiADEMK7ASABLQA2XHIBIABBCGoiACAESVxyAAsLCzUAIAAoAgQgASgCCCgCBEYEQCABIAIgAxDCggEPCyAAKAIIIgAgASACIAMgACgCACgCHBEHAAsMACAAQcO4EjYCACAACxwAIAAoAgQgASgCCCgCBEYEQCABIAIgAxDCggELC8OSBAEFfyMAQcOQAGsiBCQAAkACf0EBIAAoAgQgASgCBEZccgAaIwBBQGoiAyQAIAEgASgCACIFQQhrKAIAIgdqIQYCQCAFQQRrKAIAIgUoAgRBwrDDrQAoAgBGBEBBACAGIAcbIQEMAQsgASAGTgRAIANCADcCFCADQQA2AhAgA0HCrMOtADYCDCADIAE2AgggAyAFNgIEIANCADcCHCADQgA3AiQgA0IANwIsIANBADYCPCADQsKBwoDCgMKAwoDCgMKAwoABNwI0IAUgA0EEaiAGIAZBAUEAIAUoAgAoAhQRDAAgAygCHFxyAQsgA0IANwIUIANBADYCECADQcO8w6wANgIMIAMgATYCCCADQcKsw60ANgIEIANCADcCHCADQgA3AiQgA0IANwIsIANCADcAMyADQQA2AjwgA0EBOgA7IAUgA0EEaiAGQQFBACAFKAIAKAIYEQsAQQAhAQJAAkAgAygCKA4CAAECCyADKAIYQQAgAygCJEEBRhtBACADKAIgQQFGG0EAIAMoAixBAUYbIQEMAQsgAygCHEEBRwRAIAMoAixccgEgAygCIEEBR1xyASADKAIkQQFHXHIBCyADKAIUIQELIANBQGskAEEAIAFFXHIAGiACKAIAIgNFXHIBIARBGGpBAEE4w7wLACAEQQE6AEsgBEF/NgIgIAQgADYCHCAEIAE2AhQgBEEBNgJEIAEgBEEUaiADQQEgASgCACgCHBEHACAEKAIsIgBBAUYEQCACIAQoAiQ2AgALIABBAUYLIARBw5AAaiQADwsgBEHCmA82AgggBEHDpwM2AgQgBEHC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AgAgBSAGRlxyASADIAhGBEAgBCgCACECIAMhCAwGCyAOQQRqIgJBACAAKAIIEMKNASIIQX9GXHIEIAYgBygCAGsgCElccgYDQCAIBEAgAi0AACEFIAcgBygCACIJQQFqNgIAIAkgBToAACAIQQFrIQggAkEBaiECDAELCyAEIAQoAgBBBGoiAjYCACACIQgDQCADIAhGBEAgAyEIDAULIAgoAgBFXHIEIAhBBGohCAwACwALIAQgAjYCAAwDCyAEKAIAIQILIAIgA0chDwwDCyAHKAIAIQUMAQsLQQIhDwsgDkEQaiQAIA8LCQAgABDDmwEQXG4LEQAgAyACayIAIAQgACAESRsLNAADQCABIAJGRQRAIAQgAyABLAAAIgAgAEEASBs6AAAgBEEBaiEEIAFBAWohAQwBCwsgAQsMACACIAEgAUEASBsLKgADQCABIAJGRQRAIAMgAS0AADoAACADQQFqIQMgAUEBaiEBDAELCyABCzkAA0AgASACRkUEQCABIAEtAAAiACAAQSByIABBw5sAa0HDvwFxQcOmAUkbOgAAIAFBAWohAQwBCwsgAQsYACABIAFBIHIgAUHDmwBrQcO/AXFBw6YBSRsLOgADQCABIAJGRQRAIAEgAS0AACIAIABBw58AcSAAQcO7AGtBw78BcUHDpgFJGzoAACABQQFqIQEMAQsLIAELGQAgASABQcOfAHEgAUHDuwBrQcO/AXFBw6YBSRsLCQAgABDDlgEQXG4LNQADQCABIAJGRQRAIAQgASgCACIAIAMgAEHCgAFJGzoAACAEQQFqIQQgAUEEaiEBDAELCyABCw4AIAEgAiABQcKAAUkbw4ALKgADQCABIAJGRQRAIAMgASwAADYCACADQQRqIQMgAUEBaiEBDAELCyABCzQAA0AgASACRkUEQCABIAEoAgAiACAAQSByIABBw5sAa0FmSRs2AgAgAUEEaiEBDAELCyABC8KqAQEEfyAAKALCiAQiAQRAIAAgATYCwowEIAAoAsKQBBogARBcbgsgACgCw7wDIgEEQCAAIAE2AsKABCAAKALChAQaIAEQXG4LIAAoAsOYASIBBEAgASECIAAoAsOcASIDIAFHBEADQCADQQxrIgIoAgAiBARAIANBCGsgBDYCACADQQRrKAIAGiAEEFxuCyACIgMgAUdccgALIAAoAsOYASECCyAAIAE2AsOcASAAKALDoAEaIAIQXG4LCxMAIAEgAUEgciABQcObAGtBZkkbCzUAA0AgASACRkUEQCABIAEoAgAiACAAQcOfAHEgAEHDuwBrQWZJGzYCACABQQRqIQEMAQsLIAELFAAgASABQcOfAHEgAUHDuwBrQWZJGws2AANAAkAgAiADRlxyACACKAIAIgBBw78AS1xyACAAQQJ0KALDgDAgAXFFXHIAIAJBBGohAgwBCwsgAgs2AANAAkAgAiADRlxyACACKAIAIgBBw78ATQRAIABBAnQoAsOAMCABcVxyAQsgAkEEaiECDAELCyACC0UBAX8DQCABIAJGRQRAQQAhACADIAEoAgAiBEHDvwBNBH8gBEECdCgCw4AwBUEACzYCACADQQRqIQMgAUEEaiEBDAELCyABCyEAQQAhACACQcO/AE0EfyACQQJ0KALDgDAgAXFBAEcFQQALCw8AIAAgACgCACgCBBEBAAsOACAAQcKUETYCACAAEFxuCwkAIAAQw5kBEFxuC1EAAkAgBSwAC0EATgRAIAAgBSgCCDYCCCAAIAUpAgA3AgAMAQsgBSgCACEBIAAgBSgCBCIAEGQhAiAAQQJ0QQRqIgAEQCACIAEgAMO8XG4AAAsLCwkAIAAgBRDCjwELDAAgAEHClBE2AgAgAAvDqwQBB38jAEHDsANrIgAkACAAQcOsA2oiByADKAIcIgY2AgAgBkHDrMKXAUcEQCAGIAYoAgRBAWo2AgQLIAdBwpzCmQEQXHIhCCAFKAIEIAUsAAsiBiAGQQBIIgYbBEAgBSgCACAFIAYbKAIAIAhBLSAIKAIAKAIsEQIARiEJCyAAQQA2AsOYAyAAQgA3A8OQAyAAQQA2AsOIAyAAQgA3A8OAAyAAQQA2AsK4AyAAQgA3A8KwAyACIAkgAEHDrANqIABBw6gDaiAAQcOkA2ogAEHDoANqIABBw5ADaiAAQcOAA2ogAEHCsANqIABBwqwDahDCjQMCQAJ/An8gBSgCBCJcbiAFLAALIgYgBkEASBsiAiAAKALCrAMiB0oEQCAHIAIgB2tBAXRqIAAoAsK0AyAALADCuwMiAiACQQBIG2ogACgCw4QDIAAsAMOLAyICIAJBAEgbakEBagwBCyAHIAAoAsK0AyAALADCuwMiAiACQQBIG2ogACgCw4QDIAAsAMOLAyICIAJBAEgbakECagsiAkHDpQBJBEBBACECIABBEGoMAQsgAkECdBAoIgJFXHIBIAUtAAshBiAFKAIEIVxuIAILIgsgAEEMaiAAQQhqIAMoAgQgBSgCACAFIAbDgEEASCIFGyIMIAwgXG4gBiAFG0ECdGogCCAJIABBw6gDaiAAKALDpAMgACgCw6ADIABBw5ADaiIFIABBw4ADaiIGIABBwrADaiIIIAcQwowDIAEgCyAAKAIMIAAoAgggAyAEEMKSASACEFxuIAgQDBogBhAMGiAFEAwaAkAgACgCw6wDIgFBw6zClwFGXHIAIAEgASgCBCICQQFrNgIEIAJccgAgASABKAIAKAIIEQEACyAAQcOwA2okAA8LECEAC8KSBwFcbn8gAiAANgIAQQRBACAHGyEWIANBwoAEcSEXA0AgE0EERgRAIFxyKAIEIFxyLAALIgQgBEEASCIGGyIFQQFLBEAgAigCACEEIAVBAnRBBGsiBQRAIAQgXHIoAgAgXHIgBhtBBGogBcO8XG4AAAsgAiAEIAVqNgIACyADQcKwAXEiA0EQRwRAIAEgA0EgRgR/IAIoAgAFIAALNgIACwUCQAJAAkACQAJAAkAgCCATai0AAA4FAAEDAgQFCyABIAIoAgA2AgAMBAsgASACKAIANgIAIAZBICAGKAIAKAIsEQIAIQcgAiACKAIAIg9BBGo2AgAgDyAHNgIADAMLIFxyKAIEIFxyLAALIgcgB0EASCIHG0VccgIgXHIoAgAgXHIgBxsoAgAhByACIAIoAgAiD0EEajYCACAPIAc2AgAMAgsgF0VccgEgDCgCBCAMLAALIgcgB0EASCIQGyIPRVxyASACKAIAIQcgD0ECdCIPBEAgByAMKAIAIAwgEBsgD8O8XG4AAAsgAiAHIA9qNgIADAELIAIoAgAgBCAWaiIEIQcDQAJAIAUgB01ccgAgBkHDgAAgBygCACAGKAIAKAIMEQQARVxyACAHQQRqIQcMAQsLIA4iEEEASgRAA0ACQCAEIAdPXHIAIBBFXHIAIBBBAWshECAHQQRrIgcoAgAhDyACIAIoAgAiEUEEajYCACARIA82AgAMAQsLIBAEfyAGQTAgBigCACgCLBECAAVBAAshEiACKAIAIQ8DQCAPQQRqIREgEEEATEUEQCAPIBI2AgAgEEEBayEQIBEhDwwBCwsgAiARNgIAIA8gCTYCAAsCQCAEIAdGBEAgBkEwIAYoAgAoAiwRAgAhDyACIAIoAgAiEEEEaiIHNgIAIBAgDzYCAAwBCyALKAIEIAssAAsiDyAPQQBIIg8bBH8gCygCACALIA8bLAAABUF/CyESQQAhD0EAIRQDQCAEIAdGRQRAIAIoAgAhEQJAIA8gEkcEQCARIRAgDyERDAELIAIgEUEEaiIQNgIAIBEgXG42AgBBACERIBRBAWoiFCALKAIEIAssAAsiFSAVQQBIG08EQCAPIRIMAQtBfyESIAsoAgAiDyALIBVBAEgiFRsgFGotAABBw78ARlxyACAPIAsgFRsgFGosAAAhEgsgB0EEayIHKAIAIQ8gAiAQQQRqNgIAIBAgDzYCACARQQFqIQ8MAQsLIAIoAgAhBwsgBxDCkQELIBNBAWohEwwBCwsLwpACAQF/IwBBEGsiXG4kAAJ/IAAEQCACQcKswpcBEFxyDAELIAJBwqTClwEQXHILIQICQCABBEAgXG5BBGoiACACIAIoAgAoAiwRAwAgAyBcbigCBDYAACAAIAIgAigCACgCIBEDAAwBCyBcbkEEaiIAIAIgAigCACgCKBEDACADIFxuKAIENgAAIAAgAiACKAIAKAIcEQMACyAIIAAQw50BIAAQDBogBCACIAIoAgAoAgwRAAA2AgAgBSACIAIoAgAoAhARAAA2AgAgXG5BBGoiACACIAIoAgAoAhQRAwAgBiAAEHUgABAMGiAAIAIgAigCACgCGBEDACAHIAAQw50BIAAQDBogCSACIAIoAgAoAiQRAAA2AgAgXG5BEGokAAsFAQh/AAvDpQQBB38jAEHCsAFrIgAkACAAQcKsAWoiByADKAIcIgY2AgAgBkHDrMKXAUcEQCAGIAYoAgRBAWo2AgQLIAdBwqTCmQEQXHIhCCAFKAIEIAUsAAsiBiAGQQBIIgYbBEAgBSgCACAFIAYbLQAAIAhBLSAIKAIAKAIcEQIAQcO/AXFGIQkLIABBADYCwqABIABCADcDwpgBIABBADYCwpABIABCADcDwogBIABBADYCwoABIABCADcDeCACIAkgAEHCrAFqIABBwqgBaiAAQcKnAWogAEHCpgFqIABBwpgBaiAAQcKIAWogAEHDuABqIABBw7QAahDCkQMCQAJ/An8gBSgCBCJcbiAFLAALIgYgBkEASBsiAiAAKAJ0IgdKBEAgByACIAdrQQF0aiAAKAJ8IAAsAMKDASICIAJBAEgbaiAAKALCjAEgACwAwpMBIgIgAkEASBtqQQFqDAELIAcgACgCfCAALADCgwEiAiACQQBIG2ogACgCwowBIAAsAMKTASICIAJBAEgbakECagsiAkHDpQBJBEBBACECIABBEGoMAQsgAhAoIgJFXHIBIAUtAAshBiAFKAIEIVxuIAILIgsgAEEMaiAAQQhqIAMoAgQgBSgCACAFIAbDgEEASCIFGyIMIAwgXG4gBiAFG2ogCCAJIABBwqgBaiAALADCpwEgACwAwqYBIABBwpgBaiIFIABBwogBaiIGIABBw7gAaiIIIAcQwpADIAEgCyAAKAIMIAAoAgggAyAEEMKTASACEFxuIAgQDBogBhAMGiAFEAwaAkAgACgCwqwBIgFBw6zClwFGXHIAIAEgASgCBCICQQFrNgIEIAJccgAgASABKAIAKAIIEQEACyAAQcKwAWokAA8LECEAC8O1BgEJfyACIAA2AgAgA0HCgARxIRYDQCAUQQRGBEAgXHIoAgQgXHIsAAsiBCAEQQBIIgYbIgVBAUsEQCACKAIAIQQgBUEBayIFBEAgBCBccigCACBcciAGG0EBaiAFw7xcbgAACyACIAQgBWo2AgALIANBwrABcSIDQRBHBEAgASADQSBGBH8gAigCAAUgAAs2AgALBQJAAkACQAJAAkACQCAIIBRqLQAADgUAAQMCBAULIAEgAigCADYCAAwECyABIAIoAgA2AgAgBkEgIAYoAgAoAhwRAgAhDyACIAIoAgAiEEEBajYCACAQIA86AAAMAwsgXHIoAgQgXHIsAAsiDyAPQQBIIg8bRVxyAiBccigCACBcciAPGy0AACEPIAIgAigCACIQQQFqNgIAIBAgDzoAAAwCCyAWRVxyASAMKAIEIAwsAAsiDyAPQQBIIhEbIg9FXHIBIAIoAgAhECAPBEAgECAMKAIAIAwgERsgD8O8XG4AAAsgAiAPIBBqNgIADAELIAIoAgAgBCAHaiIEIRIDQAJAIAUgEk1ccgAgEiwAACIPQQBIXHIAIAYoAgggD0ECdGotAABBw4AAcUVccgAgEkEBaiESDAELCyAOIg9BAEoEQANAAkAgBCAST1xyACAPRVxyACAPQQFrIQ8gEkEBayISLQAAIRAgAiACKAIAIhFBAWo2AgAgESAQOgAADAELCyAPBH8gBkEwIAYoAgAoAhwRAgAFQQALIRADQCACIAIoAgAiEUEBajYCACAPQQBMRQRAIBEgEDoAACAPQQFrIQ8MAQsLIBEgCToAAAsCQCAEIBJGBEAgBkEwIAYoAgAoAhwRAgAhDyACIAIoAgAiEEEBajYCACAQIA86AAAMAQsgCygCBCALLAALIg8gD0EASCIPGwR/IAsoAgAgCyAPGywAAAVBfwshEEEAIQ9BACEVA0AgBCASRlxyAQJAIA8gEEcEQCAPIREMAQsgAiACKAIAIhBBAWo2AgAgECBcbjoAAEEAIREgFUEBaiIVIAsoAgQgCywACyITIBNBAEgbTwRAIA8hEAwBC0F/IRAgCygCACIPIAsgE0EASCITGyAVai0AAEHDvwBGXHIAIA8gCyATGyAVaiwAACEQCyASQQFrIhItAAAhDyACIAIoAgAiE0EBajYCACATIA86AAAgEUEBaiEPDAALAAsgAigCABBoCyAUQQFqIRQMAQsLC8KOAgEBfyMAQRBrIlxuJAACfyAABEAgAkHCnMKXARBccgwBCyACQcKUwpcBEFxyCyECAkAgAQRAIFxuQQRqIgAgAiACKAIAKAIsEQMAIAMgXG4oAgQ2AAAgACACIAIoAgAoAiARAwAMAQsgXG5BBGoiACACIAIoAgAoAigRAwAgAyBcbigCBDYAACAAIAIgAigCACgCHBEDAAsgCCAAEHUgABAMGiAEIAIgAigCACgCDBEAADoAACAFIAIgAigCACgCEBEAADoAACBcbkEEaiIAIAIgAigCACgCFBEDACAGIAAQdSAAEAwaIAAgAiACKAIAKAIYEQMAIAcgABB1IAAQDBogCSACIAIoAgAoAiQRAAA2AgAgXG5BEGokAAsFAQh/AAsFAQV/AAsFAQJ/AAsFAQV/AAsFAQJ/AAsFAQJ/AAsDAAALw6kOAQN/IwBBMGsiByQAIAcgATYCLCAEQQA2AgAgByADKAIcIgg2AgAgCEHDrMKXAUcEQCAIIAgoAgRBAWo2AgQLIAdBwpzCmQEQXHIhCAJAIAcoAgAiCUHDrMKXAUZccgAgCSAJKAIEIlxuQQFrNgIEIFxuXHIAIAkgCSgCACgCCBEBAAsCfwJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkAgBkHDgQBrDjkAARcEFwUXBgcXFxdcbhcXFxcODxAXFxcTFRcXFxcXFxcAAQIDAxcXARcIFxcJCxcMF1xyFwsXFxESFBYLIAAgBUEYaiAHQSxqIAIgBCAIEMOlAQwYCyAAIAVBEGogB0EsaiACIAQgCBDDpAEMFwsgAEEIaiAAKAIIKAIMEQAAIQEgByAAIAcoAiwgAiADIAQgBSABKAIAIAEgASwACyIAQQBIIgIbIgMgAyABKAIEIAAgAhtBAnRqEDQ2AiwMFgsgB0EsaiACIAQgCEECECshACAEKAIAIQECQAJAIABBAWtBHktccgAgAUEEcVxyACAFIAA2AgwMAQsgBCABQQRyNgIACwwVCyAHQcOYLikDADcDGCAHQcOQLikDADcDECAHQcOILikDADcDCCAHQcOALikDADcDACAHIAAgASACIAMgBCAFIAcgB0EgahA0NgIsDBQLIAdBw7guKQMANwMYIAdBw7AuKQMANwMQIAdBw6guKQMANwMIIAdBw6AuKQMANwMAIAcgACABIAIgAyAEIAUgByAHQSBqEDQ2AiwMEwsgB0EsaiACIAQgCEECECshACAEKAIAIQECQAJAIABBF0pccgAgAUEEcVxyACAFIAA2AggMAQsgBCABQQRyNgIACwwSCyAHQSxqIAIgBCAIQQIQKyEAIAQoAgAhAQJAAkAgAEEBa0ELS1xyACABQQRxXHIAIAUgADYCCAwBCyAEIAFBBHI2AgALDBELIAdBLGogAiAEIAhBAxArIQAgBCgCACEBAkACQCAAQcOtAkpccgAgAUEEcVxyACAFIAA2AhwMAQsgBCABQQRyNgIACwwQCyAHQSxqIAIgBCAIQQIQKyEBIAQoAgAhAAJAAkAgAUEBayIBQQtLXHIAIABBBHFccgAgBSABNgIQDAELIAQgAEEEcjYCAAsMDwsgB0EsaiACIAQgCEECECshACAEKAIAIQECQAJAIABBO0pccgAgAUEEcVxyACAFIAA2AgQMAQsgBCABQQRyNgIACwwOCyAHQSxqIQAjAEEQayIBJAAgASACNgIMA0ACQCAAIAFBDGoQDlxyACAIQQECfyAAKAIAIgIoAgwiAyACKAIQRgRAIAIgAigCACgCJBEAAAwBCyADKAIACyAIKAIAKAIMEQQARVxyACAAEGsaDAELCyAAIAFBDGoQDgRAIAQgBCgCAEECcjYCAAsgAUEQaiQADFxyCyAHQSxqIQECQCAAQQhqIAAoAggoAggRAAAiACgCBCAALAALIgMgA0EASBtBACAAKAIQIAAsABciAyADQQBIG2tGBEAgBCAEKAIAQQRyNgIADAELAkAgASACIAAgAEEYaiAIIARBABBsIgEgAEdccgAgBSgCCEEMR1xyACAFQQA2AggMAQsCQCABIABrQQxHXHIAIAUoAggiAEELSlxyACAFIABBDGo2AggLCwwMCyAHQcKAL0Esw7xcbgAAIAcgACABIAIgAyAEIAUgByAHQSxqEDQ2AiwMCwsgB0HDgC8oAgA2AhAgB0HCuC8pAwA3AwggB0HCsC8pAwA3AwAgByAAIAEgAiADIAQgBSAHIAdBFGoQNDYCLAxcbgsgB0EsaiACIAQgCEECECshACAEKAIAIQECQAJAIABBPEpccgAgAUEEcVxyACAFIAA2AgAMAQsgBCABQQRyNgIACwwJCyAHQcOoLykDADcDGCAHQcOgLykDADcDECAHQcOYLykDADcDCCAHQcOQLykDADcDACAHIAAgASACIAMgBCAFIAcgB0EgahA0NgIsDAgLIAdBLGogAiAEIAhBARArIQAgBCgCACEBAkACQCAAQQZKXHIAIAFBBHFccgAgBSAANgIYDAELIAQgAUEEcjYCAAsMBwsgACABIAIgAyAEIAUgACgCACgCFBEFAAwHCyAAQQhqIAAoAggoAhgRAAAhASAHIAAgBygCLCACIAMgBCAFIAEoAgAgASABLAALIgBBAEgiAhsiAyADIAEoAgQgACACG0ECdGoQNDYCLAwFCyAFQRRqIAdBLGogAiAEIAgQw6MBDAQLIAdBLGogAiAEIAhBBBArIQAgBC0AAEEEcUUEQCAFIABBw6wOazYCFAsMAwsgBkElRlxyAQsgBCAEKAIAQQRyNgIADAELIwBBEGsiACQAIAAgAjYCDAJAIAQCf0EGIAdBLGoiAiAAQQxqIgMQDlxyABpBBCAIAn8gAigCACIBKAIMIgUgASgCEEYEQCABIAEoAgAoAiQRAAAMAQsgBSgCAAtBACAIKAIAKAI0EQQAQSVHXHIAGiACEGsgAxAORVxyAUECCyAEKAIAcjYCAAsgAEEQaiQACyAHKAIsCyAHQTBqJAALwpYBAQF/IwBBEGsiACQAIAAgATYCDCAAQQhqIgYgAygCHCIBNgIAIAFBw6zClwFHBEAgASABKAIEQQFqNgIECyAGQcKcwpkBEFxyIQMCQCAAKAIIIgFBw6zClwFGXHIAIAEgASgCBCIGQQFrNgIEIAZccgAgASABKAIAKAIIEQEACyAFQRRqIABBDGogAiAEIAMQw6MBIAAoAgwgAEEQaiQAC8KYAQECfyMAQRBrIgYkACAGIAE2AgwgBkEIaiIHIAMoAhwiATYCACABQcOswpcBRwRAIAEgASgCBEEBajYCBAsgB0HCnMKZARBcciEDAkAgBigCCCIBQcOswpcBRlxyACABIAEoAgQiB0EBazYCBCAHXHIAIAEgASgCACgCCBEBAAsgACAFQRBqIAZBDGogAiAEIAMQw6QBIAYoAgwgBkEQaiQAC8KYAQECfyMAQRBrIgYkACAGIAE2AgwgBkEIaiIHIAMoAhwiATYCACABQcOswpcBRwRAIAEgASgCBEEBajYCBAsgB0HCnMKZARBcciEDAkAgBigCCCIBQcOswpcBRlxyACABIAEoAgQiB0EBazYCBCAHXHIAIAEgASgCACgCCBEBAAsgACAFQRhqIAZBDGogAiAEIAMQw6UBIAYoAgwgBkEQaiQAC0YAIAAgASACIAMgBCAFIABBCGogACgCCCgCFBEAACIAKAIAIAAgACwACyIBQQBIIgIbIgMgAyAAKAIEIAEgAhtBAnRqEDQLVAEBfyMAQSBrIgYkACAGQcOoLykDADcDGCAGQcOgLykDADcDECAGQcOYLykDADcDCCAGQcOQLykDADcDACAAIAEgAiADIAQgBSAGIAZBIGoiARA0IAEkAAvCmg4BA38jAEEQayIHJAAgByABNgIMIARBADYCACAHIAMoAhwiCDYCACAIQcOswpcBRwRAIAggCCgCBEEBajYCBAsgB0HCpMKZARBcciEIAkAgBygCACIJQcOswpcBRlxyACAJIAkoAgQiXG5BAWs2AgQgXG5ccgAgCSAJKAIAKAIIEQEACwJ/AkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQCAGQcOBAGsOOQABFwQXBRcGBxcXF1xuFxcXFw4PEBcXFxMVFxcXFxcXFwABAgMDFxcBFwgXFwkLFwwXXHIXCxcXERIUFgsgACAFQRhqIAdBDGogAiAEIAgQw6kBDBgLIAAgBUEQaiAHQQxqIAIgBCAIEMOoAQwXCyAAQQhqIAAoAggoAgwRAAAhASAHIAAgBygCDCACIAMgBCAFIAEoAgAgASABLAALIgBBAEgiAhsiAyADIAEoAgQgACACG2oQNTYCDAwWCyAHQQxqIAIgBCAIQQIQLCEAIAQoAgAhAQJAAkAgAEEBa0EeS1xyACABQQRxXHIAIAUgADYCDAwBCyAEIAFBBHI2AgALDBULIAdCwqXDmsK9wqnDgsOsw4vCksO5ADcDACAHIAAgASACIAMgBCAFIAcgB0EIahA1NgIMDBQLIAdCwqXCssK1wqnDksKtw4vCksOkADcDACAHIAAgASACIAMgBCAFIAcgB0EIahA1NgIMDBMLIAdBDGogAiAEIAhBAhAsIQAgBCgCACEBAkACQCAAQRdKXHIAIAFBBHFccgAgBSAANgIIDAELIAQgAUEEcjYCAAsMEgsgB0EMaiACIAQgCEECECwhACAEKAIAIQECQAJAIABBAWtBC0tccgAgAUEEcVxyACAFIAA2AggMAQsgBCABQQRyNgIACwwRCyAHQQxqIAIgBCAIQQMQLCEAIAQoAgAhAQJAAkAgAEHDrQJKXHIAIAFBBHFccgAgBSAANgIcDAELIAQgAUEEcjYCAAsMEAsgB0EMaiACIAQgCEECECwhASAEKAIAIQACQAJAIAFBAWsiAUELS1xyACAAQQRxXHIAIAUgATYCEAwBCyAEIABBBHI2AgALDA8LIAdBDGogAiAEIAhBAhAsIQAgBCgCACEBAkACQCAAQTtKXHIAIAFBBHFccgAgBSAANgIEDAELIAQgAUEEcjYCAAsMDgsgB0EMaiEAIwBBEGsiASQAIAEgAjYCDANAAkAgACABQQxqEA9ccgACfyAAKAIAIgIoAgwiAyACKAIQRgRAIAIgAigCACgCJBEAAAwBCyADLQAAC8OAIgJBAEhccgAgCCgCCCACQQJ0ai0AAEEBcUVccgAgABBtGgwBCwsgACABQQxqEA8EQCAEIAQoAgBBAnI2AgALIAFBEGokAAxccgsgB0EMaiEBAkAgAEEIaiAAKAIIKAIIEQAAIgAoAgQgACwACyIDIANBAEgbQQAgACgCECAALAAXIgMgA0EASBtrRgRAIAQgBCgCAEEEcjYCAAwBCwJAIAEgAiAAIABBGGogCCAEQQAQbiIBIABHXHIAIAUoAghBDEdccgAgBUEANgIIDAELAkAgASAAa0EMR1xyACAFKAIIIgBBC0pccgAgBSAAQQxqNgIICwsMDAsgB0HCqC4oAAA2AAcgB0HCoS4pAAA3AwAgByAAIAEgAiADIAQgBSAHIAdBC2oQNTYCDAwLCyAHQcKwLi0AADoABCAHQcKsLigAADYCACAHIAAgASACIAMgBCAFIAcgB0EFahA1NgIMDFxuCyAHQQxqIAIgBCAIQQIQLCEAIAQoAgAhAQJAAkAgAEE8SlxyACABQQRxXHIAIAUgADYCAAwBCyAEIAFBBHI2AgALDAkLIAdCwqXCkMOpwqnDksOJw47CksOTADcDACAHIAAgASACIAMgBCAFIAcgB0EIahA1NgIMDAgLIAdBDGogAiAEIAhBARAsIQAgBCgCACEBAkACQCAAQQZKXHIAIAFBBHFccgAgBSAANgIYDAELIAQgAUEEcjYCAAsMBwsgACABIAIgAyAEIAUgACgCACgCFBEFAAwHCyAAQQhqIAAoAggoAhgRAAAhASAHIAAgBygCDCACIAMgBCAFIAEoAgAgASABLAALIgBBAEgiAhsiAyADIAEoAgQgACACG2oQNTYCDAwFCyAFQRRqIAdBDGogAiAEIAgQw6cBDAQLIAdBDGogAiAEIAhBBBAsIQAgBC0AAEEEcUUEQCAFIABBw6wOazYCFAsMAwsgBkElRlxyAQsgBCAEKAIAQQRyNgIADAELIwBBEGsiACQAIAAgAjYCDAJAIAQCf0EGIAdBDGoiAiAAQQxqIgMQD1xyABpBBCAIAn8gAigCACIBKAIMIgUgASgCEEYEQCABIAEoAgAoAiQRAAAMAQsgBS0AAAvDgEEAIAgoAgAoAiQRBABBJUdccgAaIAIQbSADEA9FXHIBQQILIAQoAgByNgIACyAAQRBqJAALIAcoAgwLIAdBEGokAAvClgEBAX8jAEEQayIAJAAgACABNgIMIABBCGoiBiADKAIcIgE2AgAgAUHDrMKXAUcEQCABIAEoAgRBAWo2AgQLIAZBwqTCmQEQXHIhAwJAIAAoAggiAUHDrMKXAUZccgAgASABKAIEIgZBAWs2AgQgBlxyACABIAEoAgAoAggRAQALIAVBFGogAEEMaiACIAQgAxDDpwEgACgCDCAAQRBqJAALwpgBAQJ/IwBBEGsiBiQAIAYgATYCDCAGQQhqIgcgAygCHCIBNgIAIAFBw6zClwFHBEAgASABKAIEQQFqNgIECyAHQcKkwpkBEFxyIQMCQCAGKAIIIgFBw6zClwFGXHIAIAEgASgCBCIHQQFrNgIEIAdccgAgASABKAIAKAIIEQEACyAAIAVBEGogBkEMaiACIAQgAxDDqAEgBigCDCAGQRBqJAALwpgBAQJ/IwBBEGsiBiQAIAYgATYCDCAGQQhqIgcgAygCHCIBNgIAIAFBw6zClwFHBEAgASABKAIEQQFqNgIECyAHQcKkwpkBEFxyIQMCQCAGKAIIIgFBw6zClwFGXHIAIAEgASgCBCIHQQFrNgIEIAdccgAgASABKAIAKAIIEQEACyAAIAVBGGogBkEMaiACIAQgAxDDqQEgBigCDCAGQRBqJAALQwAgACABIAIgAyAEIAUgAEEIaiAAKAIIKAIUEQAAIgAoAgAgACAALAALIgFBAEgiAhsiAyADIAAoAgQgASACG2oQNQs7AQF/IwBBEGsiBiQAIAZCwqXCkMOpwqnDksOJw47CksOTADcDCCAAIAEgAiADIAQgBSAGQQhqIAZBEGoiARA1IAEkAAsrAQF/IAIgAigCBCIFQcK1w7t+cUHCiARyNgIEIAEgAiADIAQQw6sBIAIgBTYCBAsFAQh/AAsFAQh/AAsFAQV/AAtccgAgASACIAMgBBDDqwELBwIGfwF+AAvDuwMBB38jAEHCkAFrIgUkACACKAIEIgZBw4oAcSIIQQhGIQcgBUHCgwFqIQACfwJAIARBAE5ccgAgB1xyACAEIAhBw4AARlxyARogBUEtOgDCgwEgBUHChAFqIQBBACAEawwBCyAECyFcbkEQQVxuIAcbIQsgCEHDgABGIQkCQCAHXHIAIAlccgAgBEEASFxyACAGQcKAEHFFXHIAIABBKzoAACAAQQFqIQALQQggCyAJGyEHAkAgBEVccgAgBkHCgARxRVxyACAIQcOAAEYEQCAAQTA6AAAgAEEBaiEADAELIAhBCEdccgAgAEEwOgAAIABBw5gAQcO4ACAGQcKAwoABcRs6AAEgAEECaiEACyAFQcO4AGogACAFQcKQAWogXG4gBxBqAkAgBkHCiMKAAXFBwojCgAFGBEADQCAAIAUoAngiBEZccgIgACAALQAAIgRBIGsgBCAEQcOhAGtBw78BcUEGSRs6AAAgAEEBaiEADAALAAsgBSgCeCEECyAFQcKDAWoiBiAEIAIQaSEIIAVBBGoiByACKAIcIgA2AgAgAEHDrMKXAUcEQCAAIAAoAgRBAWo2AgQLIAYgCCAEIAVBEGoiBCAFQQxqIAVBCGogBxDDrQECQCAFKAIEIgBBw6zClwFGXHIAIAAgACgCBCIGQQFrNgIEIAZccgAgACAAKAIAKAIIEQEACyABIAQgBSgCDCAFKAIIIAIgAxDCkgEgBUHCkAFqJAALw4YBAQV/IwBBEGsiBSQAIwBBEGsiBCQAIwBBEGsiAyQAIAMgAjYCDANAIAAgAUcEQCAAKAIAIQYCQCADKAIMIgJFXHIAAn8gAigCGCIHIAIoAhxGBEAgAiAGIAIoAgAoAjQRAgAMAQsgByAGNgIAIAIgB0EEajYCGCAGC0F/R1xyACADQQA2AgwLIABBBGohAAwBCwsgBCAANgIIIAQgAygCDDYCDCADQRBqJAAgBSAEKQIINwIIIARBEGokACAFKAIMIAVBEGokAAvDqgEBAn8jAEEQayIFJAACQCACLQAEQQFxRQRAIAAgASACIAMgBCAAKAIAKAIYEQYAIQIMAQsgBUEEaiIAIAIoAhwiAjYCACACQcOswpcBRwRAIAIgAigCBEEBajYCBAsgAEHDpMKZARBcciEDAkAgBSgCBCICQcOswpcBRlxyACACIAIoAgQiBkEBazYCBCAGXHIAIAIgAigCACgCCBEBAAsgACADIAMoAgBBGEEcIAQbaigCABEDACAFKAIEIAAgBSwADyICQQBIIgMbIgQgBCAFKAIIIAIgAxtBAnRqIAEQwqwDIQIgABAMGgsgBUEQaiQAIAILKwEBfyACIAIoAgQiBUHCtcO7fnFBwogEcjYCBCABIAIgAyAEEMOuASACIAU2AgQLBQEIfwALBQEIfwALBQEFfwALXHIAIAEgAiADIAQQw64BCwcCBn8BfgALw7MDAQd/IwBBQGoiBSQAIAIoAgQiBkHDigBxIghBCEYhByAFQTNqIQACfwJAIARBAE5ccgAgB1xyACAEIAhBw4AARlxyARogBUEtOgAzIAVBNGohAEEAIARrDAELIAQLIVxuQRBBXG4gBxshCyAIQcOAAEYhCQJAIAdccgAgCVxyACAEQQBIXHIAIAZBwoAQcUVccgAgAEErOgAAIABBAWohAAtBCCALIAkbIQcCQCAERVxyACAGQcKABHFFXHIAIAhBw4AARgRAIABBMDoAACAAQQFqIQAMAQsgCEEIR1xyACAAQTA6AAAgAEHDmABBw7gAIAZBwoDCgAFxGzoAASAAQQJqIQALIAVBKGogACAFQUBrIFxuIAcQagJAIAZBwojCgAFxQcKIwoABRgRAA0AgACAFKAIoIgRGXHICIAAgAC0AACIEQSBrIAQgBEHDoQBrQcO/AXFBBkkbOgAAIABBAWohAAwACwALIAUoAighBAsgBUEzaiIGIAQgAhBpIQggBUEEaiIHIAIoAhwiADYCACAAQcOswpcBRwRAIAAgACgCBEEBajYCBAsgBiAIIAQgBUEQaiIEIAVBDGogBUEIaiAHEMOwAQJAIAUoAgQiAEHDrMKXAUZccgAgACAAKAIEIgZBAWs2AgQgBlxyACAAIAAoAgAoAggRAQALIAEgBCAFKAIMIAUoAgggAiADEMKTASAFQUBrJAALfAEDfyMAQRBrIgUkACMAQRBrIgMkACMAQRBrIgQkACAEIAI2AgwDQCAAIAFHBEAgBEEMaiAALAAAEMKTAiAAQQFqIQAMAQsLIAMgADYCCCADIAQoAgw2AgwgBEEQaiQAIAUgAykCCDcCCCADQRBqJAAgBSgCDCAFQRBqJAALw6cBAQJ/IwBBEGsiBSQAAkAgAi0ABEEBcUUEQCAAIAEgAiADIAQgACgCACgCGBEGACECDAELIAVBBGoiACACKAIcIgI2AgAgAkHDrMKXAUcEQCACIAIoAgRBAWo2AgQLIABBw5zCmQEQXHIhAwJAIAUoAgQiAkHDrMKXAUZccgAgAiACKAIEIgZBAWs2AgQgBlxyACACIAIoAgAoAggRAQALIAAgAyADKAIAQRhBHCAEG2ooAgARAwAgBSgCBCAAIAUsAA8iAkEASCIDGyIEIAQgBSgCCCACIAMbaiABEMK1AyECIAAQDBoLIAVBEGokACACCykBAX8jAEEQayIDJAAgACACLAAAIAEgAGsQTyIAIAEgABsgA0EQaiQAC0kBAn8jAEEQayIGJAAgAyADKAIEIgdBwrXDv35xQQhyNgIEIAEgAiADIAQgBkEMahDDswEgAyAHNgIEIAUgBigCDDYCACAGQRBqJAALw6IFAgJ/AX4CfyMAQcOwAmsiACQAIAAgAjYCw6gCIAAgATYCw6wCIABBw5wBaiADIABBw7ABaiAAQcOsAWogAEHDqAFqEMKVASAAQQA2AsOYASAAQgA3A8OQASAAQcOQAWoiAUFcbhAeIAAgACgCw5ABIAEgACwAw5sBQQBIGyIBNgLDjAEgACAAQSBqNgIcIABBADYCGCAAQQE6ABcgAEHDhQA6ABZBACECA0ACQAJAAkAgAEHDrAJqIABBw6gCahAOXHIAIAAoAsOMASABIAAoAsOUASAALADDmwEiAyADQQBIGyIDakYEQCAAQcOQAWoiASADQQF0EB4gAUFcbiAAKALDmAFBw7/Dv8O/w78HcUEBayAALADDmwFBAE4bEB4gACAAKALDkAEgASAALADDmwFBAEgbIgEgA2o2AsOMAQsCfyAAKALDrAIiAygCDCIGIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIAYoAgALIABBF2ogAEEWaiABIABBw4wBaiAAKALDrAEgACgCw6gBIABBw5wBaiAAQSBqIABBHGogAEEYaiAAQcOwAWoQwpQBXHIAIAJccgFBACECIAAoAsOMASABayIGQQBMXHICAkACQCABLQAAIgNBK2siBw4DAQABAAsgA0EuRlxyAkEBIQIgA0Ewa0HDvwFxQVxuSVxyAwwBCyAGQQFGXHICAkAgBw4DAAMAAwsgAS0AASIDQS5GXHIBQQEhAiADQTBrQcO/AXFBCU1ccgILAkAgACgCw6ABIAAsAMOnASICIAJBAEgbRVxyACAALQAXQQFxRVxyACAAKAIcIgIgAEEgamtBwp8BSlxyACAAIAJBBGo2AhwgAiAAKAIYNgIACyAAIAEgACgCw4wBIAQQw7UBIAApAwAhCCAFIAApAwg3AwggBSAINwMAIABBw5wBaiAAQSBqIAAoAhwgBBAgIABBw6wCaiAAQcOoAmoQDgRAIAQgBCgCAEECcjYCAAsgACgCw6wCIABBw5ABahAMGiAAQcOcAWoQDBogAEHDsAJqJAAMAwtBASECCyAAKALDrAIQEhoMAAsACwvDiwUBAn8CfyMAQcOgAmsiACQAIAAgAjYCw5gCIAAgATYCw5wCIABBw4wBaiADIABBw6ABaiAAQcOcAWogAEHDmAFqEMKVASAAQQA2AsOIASAAQgA3A8OAASAAQcOAAWoiAUFcbhAeIAAgACgCw4ABIAEgACwAw4sBQQBIGyIBNgLCvAEgACAAQRBqNgIMIABBADYCCCAAQQE6AAcgAEHDhQA6AAZBACECA0ACQAJAAkAgAEHDnAJqIABBw5gCahAOXHIAIAAoAsK8ASABIAAoAsOEASAALADDiwEiAyADQQBIGyIDakYEQCAAQcOAAWoiASADQQF0EB4gAUFcbiAAKALDiAFBw7/Dv8O/w78HcUEBayAALADDiwFBAE4bEB4gACAAKALDgAEgASAALADDiwFBAEgbIgEgA2o2AsK8AQsCfyAAKALDnAIiAygCDCIGIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIAYoAgALIABBB2ogAEEGaiABIABBwrwBaiAAKALDnAEgACgCw5gBIABBw4wBaiAAQRBqIABBDGogAEEIaiAAQcOgAWoQwpQBXHIAIAJccgFBACECIAAoAsK8ASABayIGQQBMXHICAkACQCABLQAAIgNBK2siBw4DAQABAAsgA0EuRlxyAkEBIQIgA0Ewa0HDvwFxQVxuSVxyAwwBCyAGQQFGXHICAkAgBw4DAAMAAwsgAS0AASIDQS5GXHIBQQEhAiADQTBrQcO/AXFBCU1ccgILAkAgACgCw5ABIAAsAMOXASICIAJBAEgbRVxyACAALQAHQQFxRVxyACAAKAIMIgIgAEEQamtBwp8BSlxyACAAIAJBBGo2AgwgAiAAKAIINgIACyAFIAEgACgCwrwBIAQQw7YBOQMAIABBw4wBaiAAQRBqIAAoAgwgBBAgIABBw5wCaiAAQcOYAmoQDgRAIAQgBCgCAEECcjYCAAsgACgCw5wCIABBw4ABahAMGiAAQcOMAWoQDBogAEHDoAJqJAAMAwtBASECCyAAKALDnAIQEhoMAAsACwvDiwUBAn8CfyMAQcOgAmsiACQAIAAgAjYCw5gCIAAgATYCw5wCIABBw4wBaiADIABBw6ABaiAAQcOcAWogAEHDmAFqEMKVASAAQQA2AsOIASAAQgA3A8OAASAAQcOAAWoiAUFcbhAeIAAgACgCw4ABIAEgACwAw4sBQQBIGyIBNgLCvAEgACAAQRBqNgIMIABBADYCCCAAQQE6AAcgAEHDhQA6AAZBACECA0ACQAJAAkAgAEHDnAJqIABBw5gCahAOXHIAIAAoAsK8ASABIAAoAsOEASAALADDiwEiAyADQQBIGyIDakYEQCAAQcOAAWoiASADQQF0EB4gAUFcbiAAKALDiAFBw7/Dv8O/w78HcUEBayAALADDiwFBAE4bEB4gACAAKALDgAEgASAALADDiwFBAEgbIgEgA2o2AsK8AQsCfyAAKALDnAIiAygCDCIGIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIAYoAgALIABBB2ogAEEGaiABIABBwrwBaiAAKALDnAEgACgCw5gBIABBw4wBaiAAQRBqIABBDGogAEEIaiAAQcOgAWoQwpQBXHIAIAJccgFBACECIAAoAsK8ASABayIGQQBMXHICAkACQCABLQAAIgNBK2siBw4DAQABAAsgA0EuRlxyAkEBIQIgA0Ewa0HDvwFxQVxuSVxyAwwBCyAGQQFGXHICAkAgBw4DAAMAAwsgAS0AASIDQS5GXHIBQQEhAiADQTBrQcO/AXFBCU1ccgILAkAgACgCw5ABIAAsAMOXASICIAJBAEgbRVxyACAALQAHQQFxRVxyACAAKAIMIgIgAEEQamtBwp8BSlxyACAAIAJBBGo2AgwgAiAAKAIINgIACyAFIAEgACgCwrwBIAQQw7gBOAIAIABBw4wBaiAAQRBqIAAoAgwgBBAgIABBw5wCaiAAQcOYAmoQDgRAIAQgBCgCAEECcjYCAAsgACgCw5wCIABBw4ABahAMGiAAQcOMAWoQDBogAEHDoAJqJAAMAwtBASECCyAAKALDnAIQEhoMAAsACwvDk1xuAgh/BH4jAEHCsAJrIgYkACAGIAI2AsKoAiAGIAE2AsKsAiADEC4hASAGQRBqIgIgAygCHCIANgIAIABBw6zClwFHBEAgACAAKAIEQQFqNgIECyACQcOkwpkBEFxyIQACQCAGKAIQIghBw6zClwFGXHIAIAggCCgCBCIHQQFrNgIEIAdccgAgCCAIKAIAKAIIEQEACyAAIAAoAgAoAhARAAAhXG4gBkHCnAJqIAAgACgCACgCFBEDACADIAZBwrABahBUIQMCQCAGQcKsAmogBkHCqAJqEA5FBEADQCACIAZBEGprQcKfAUohCAJAA0AgBigCwqACIAYsAMKnAiIAIABBAEgbRVxyAQJ/IAYoAsKsAiIAKAIMIgcgACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgBygCAAsgXG5HXHIBIAYoAsKsAhASGiAIXHIACyACQQA2AgAgAkEEaiECDAELCwJ/IAYoAsKsAiIAKAIMIgggACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgCCgCAAshACADKAJkIQgCfyADKAJgIgcgAEcEQEEAIAAgCEdccgEaCyAGKALCrAIQEhogACAIRiAAIAdHcgshDCAGQcKsAmogBkHCqAJqEA4EQCAEIAQoAgBBBnI2AgAgBUIANwMADAILQRAhAEEAIQgCQAJAIAFBEEcEQCABBEAgASEADAMLAn8gBigCwqwCIgAoAgwiASAAKAIQRgRAIAAgACgCACgCJBEAAAwBCyABKAIACyADKAIARwRAQVxuIQAMAwsgBigCwqwCEBIaIAZBwqwCaiAGQcKoAmoQDkUEQAJ/IAYoAsKsAiIAKAIMIgEgACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgASgCAAsiACADKAJYRlxyAiAAIAMoAlxcRlxyAkEBIQhBCCEADAMLIAQgBCgCAEECcjYCACAFQgA3AwAMBAsCfyAGKALCrAIiASgCDCIHIAEoAhBGBEAgASABKAIAKAIkEQAADAELIAcoAgALIAMoAgBHXHIBIAYoAsKsAhASGiAGQcKsAmogBkHCqAJqEA4EQCAEIAQoAgBBAnI2AgAgBUIANwMADAQLAn8gBigCwqwCIgEoAgwiByABKAIQRgRAIAEgASgCACgCJBEAAAwBCyAHKAIACyIBIAMoAlhGXHIAIAEgAygCXFxGXHIAQQEhCAwBCyAGKALCrAIQEhpBECEACyAAwq0hECAAQRBGIVxyQQAhAQNAAkAgBkHCrAJqIAZBwqgCahAOXHIAAkACQAJ/IAYoAsKsAiIHKAIMIgkgBygCEEYEQCAHIAcoAgAoAiQRAAAMAQsgCSgCAAsiByBcbkdccgAgBigCwqACIAYsAMKnAiIJIAlBAEgbRVxyACACIAZBEGprQcKfAUpccgEgAiABNgIAIAJBBGohAkEAIQEMAQsgAyAHEFMiB0EVSlxyASAHQQZrIAcgB0EPShsgByBcchsiByAATlxyASAGIBBCACAOQgAQGEEBIQggBikDACEOIAFBAWohASAGKQMIQgBSBH9BAQVCACAOIA4gB8KsIg98Ig5Wwq0gD0I/wod8Ig9CAcKDfSIRIA/ChUIAUiARQgBTcgsgC0EBcXIhCwsgBigCwqwCEBIaDAELCyAFIAhBf3MgC3JBAXEEfiAEIAQoAgBBBHI2AgBCACAIwq19BUIAIA59IA4gDBsLNwMAAkAgBigCwqACIAYsAMKnAiIAIABBAEgbRVxyACACIAZBEGprQcKfAUpccgAgAiABNgIAIAJBBGohAgsgBkHCnAJqIAZBEGogAiAEECAgBkHCrAJqIAZBwqgCahAORVxyASAEIAQoAgBBAnI2AgAMAQsgBCAEKAIAQQZyNgIAIAVCADcDAAsgBigCwqwCIAZBwpwCahAMGiAGQcKwAmokAAvCi1xuAQl/IwBBwqACayIAJAAgACACNgLCmAIgACABNgLCnAIgAxAuIQYgACADKAIcIgE2AgAgAUHDrMKXAUcEQCABIAEoAgRBAWo2AgQLIABBw6TCmQEQXHIhAQJAIAAoAgAiAkHDrMKXAUZccgAgAiACKAIEIgtBAWs2AgQgC1xyACACIAIoAgAoAggRAQALIAEgASgCACgCEBEAACELIABBwowCaiABIAEoAgAoAhQRAwAgAyAAQcKgAWoQVCEDAkAgAEHCnAJqIABBwpgCahAORQRAIAAhAgNAIAIgAGtBwp8BSiEIAkADQCAAKALCkAIgACwAwpcCIgEgAUEASBtFXHIBAn8gACgCwpwCIgEoAgwiByABKAIQRgRAIAEgASgCACgCJBEAAAwBCyAHKAIACyALR1xyASAAKALCnAIQEhogCFxyAAsgAkEANgIAIAJBBGohAgwBCwsCfyAAKALCnAIiASgCDCIIIAEoAhBGBEAgASABKAIAKAIkEQAADAELIAgoAgALIQEgAygCZCEIAn8gAygCYCIHIAFHBEBBACABIAhHXHIBGgsgACgCwpwCEBIaIAEgCEYgASAHR3ILIQggAEHCnAJqIABBwpgCahAOBEAgBCAEKAIAQQZyNgIAIAVBADsBAAwCC0EQIQECQAJAIAZBEEcEQCAGBEAgBiEBDAMLAn8gACgCwpwCIgYoAgwiByAGKAIQRgRAIAYgBigCACgCJBEAAAwBCyAHKAIACyADKAIARwRAQVxuIQEMAwsgACgCwpwCEBIaIABBwpwCaiAAQcKYAmoQDkUEQAJ/IAAoAsKcAiIGKAIMIgcgBigCEEYEQCAGIAYoAgAoAiQRAAAMAQsgBygCAAsiBiADKAJYRlxyAiAGIAMoAlxcRlxyAkEBIQlBCCEBDAMLIAQgBCgCAEECcjYCACAFQQA7AQAMBAsCfyAAKALCnAIiBigCDCIHIAYoAhBGBEAgBiAGKAIAKAIkEQAADAELIAcoAgALIAMoAgBHXHIBIAAoAsKcAhASGiAAQcKcAmogAEHCmAJqEA4EQCAEIAQoAgBBAnI2AgAgBUEAOwEADAQLAn8gACgCwpwCIgYoAgwiByAGKAIQRgRAIAYgBigCACgCJBEAAAwBCyAHKAIACyIGIAMoAlhGXHIAIAYgAygCXFxGXHIAQQEhCQwBCyAAKALCnAIQEhoLIAFBEEYhBwNAAkAgAEHCnAJqIABBwpgCahAOXHIAAkACQAJ/IAAoAsKcAiIGKAIMIlxuIAYoAhBGBEAgBiAGKAIAKAIkEQAADAELIFxuKAIACyIGIAtHXHIAIAAoAsKQAiAALADClwIiXG4gXG5BAEgbRVxyACACIABrQcKfAUpccgEgAiAMNgIAIAJBBGohAkEAIQwMAQsgAyAGEFMiBkEVSlxyASAGQQZrIAYgBkEPShsgBiAHGyJcbiABTlxyASABIFxyQcO/w78DcWwiBiAGIFxuaiIJIAZBw7/DvwNLGyFcciAOIAYgCXJBw7/DvwNLciEOQQEhCSAMQQFqIQwLIAAoAsKcAhASGgwBCwsgBSAJQX9zIA5yQQFxBH8gBCAEKAIAQQRyNgIAQQAgCWsFQQAgXHJrIFxyIAgbCzsBAAJAIAAoAsKQAiAALADClwIiASABQQBIG0VccgAgAiAAa0HCnwFKXHIAIAIgDDYCACACQQRqIQILIABBwowCaiAAIAIgBBAgIABBwpwCaiAAQcKYAmoQDkVccgEgBCAEKAIAQQJyNgIADAELIAQgBCgCAEEGcjYCACAFQQA7AQALIAAoAsKcAiAAQcKMAmoQDBogAEHCoAJqJAALw5QLAgh/BH4jAEHCsAJrIgYkACAGIAI2AsKoAiAGIAE2AsKsAiADEC4hASAGQRBqIgIgAygCHCIANgIAIABBw6zClwFHBEAgACAAKAIEQQFqNgIECyACQcOkwpkBEFxyIQACQCAGKAIQIghBw6zClwFGXHIAIAggCCgCBCIHQQFrNgIEIAdccgAgCCAIKAIAKAIIEQEACyAAIAAoAgAoAhARAAAhXG4gBkHCnAJqIAAgACgCACgCFBEDACADIAZBwrABahBUIQMCQCAGQcKsAmogBkHCqAJqEA5FBEADQCACIAZBEGprQcKfAUohCAJAA0AgBigCwqACIAYsAMKnAiIAIABBAEgbRVxyAQJ/IAYoAsKsAiIAKAIMIgcgACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgBygCAAsgXG5HXHIBIAYoAsKsAhASGiAIXHIACyACQQA2AgAgAkEEaiECDAELCwJ/IAYoAsKsAiIAKAIMIgggACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgCCgCAAshACADKAJkIQgCfyADKAJgIgcgAEcEQEEAIAAgCEdccgEaCyAGKALCrAIQEhogACAIRiAAIAdHcgshCyAGQcKsAmogBkHCqAJqEA4EQCAEIAQoAgBBBnI2AgAgBUIANwMADAILQRAhAEEAIQgCQAJAIAFBEEcEQCABBEAgASEADAMLAn8gBigCwqwCIgAoAgwiASAAKAIQRgRAIAAgACgCACgCJBEAAAwBCyABKAIACyADKAIARwRAQVxuIQAMAwsgBigCwqwCEBIaIAZBwqwCaiAGQcKoAmoQDkUEQAJ/IAYoAsKsAiIAKAIMIgEgACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgASgCAAsiACADKAJYRlxyAiAAIAMoAlxcRlxyAkEBIQhBCCEADAMLIAQgBCgCAEECcjYCACAFQgA3AwAMBAsCfyAGKALCrAIiASgCDCIHIAEoAhBGBEAgASABKAIAKAIkEQAADAELIAcoAgALIAMoAgBHXHIBIAYoAsKsAhASGiAGQcKsAmogBkHCqAJqEA4EQCAEIAQoAgBBAnI2AgAgBUIANwMADAQLAn8gBigCwqwCIgEoAgwiByABKAIQRgRAIAEgASgCACgCJBEAAAwBCyAHKAIACyIBIAMoAlhGXHIAIAEgAygCXFxGXHIAQQEhCAwBCyAGKALCrAIQEhpBECEACyAAwq0hECAAQRBGIVxyQQAhAQNAAkAgBkHCrAJqIAZBwqgCahAOXHIAAkACQAJ/IAYoAsKsAiIHKAIMIgkgBygCEEYEQCAHIAcoAgAoAiQRAAAMAQsgCSgCAAsiByBcbkdccgAgBigCwqACIAYsAMKnAiIJIAlBAEgbRVxyACACIAZBEGprQcKfAUpccgEgAiABNgIAIAJBBGohAkEAIQEMAQsgAyAHEFMiB0EVSlxyASAHQQZrIAcgB0EPShsgByBcchsiByAATlxyASAGIBBCACAOQgAQGEEBIQggBikDACEOIAFBAWohASAGKQMIQgBSBH9BAQVCACAOIA4gB8KsIg98Ig5Wwq0gD0I/wod8Ig9CAcKDfSIRIA/ChUIAUiARQgBTcgsgDEEBcXIhDAsgBigCwqwCEBIaDAELCwJAIAhFBEAgBCAEKAIAQQRyNgIAQgAhDgwBCyAMQQFxBEAgBCAEKAIAQQRyNgIAQsKAwoDCgMKAwoDCgMKAwoDCgH9Cw7/Dv8O/w7/Dv8O/w7/Dv8O/ACALGyEODAELIAtFBEAgDkIAWVxyASAEIAQoAgBBBHI2AgBCw7/Dv8O/w7/Dv8O/w7/Dv8O/ACEODAELIA5CwoHCgMKAwoDCgMKAwoDCgMKAf1oEQCAEIAQoAgBBBHI2AgBCwoDCgMKAwoDCgMKAwoDCgMKAfyEODAELQgAgDn0hDgsgBSAONwMAAkAgBigCwqACIAYsAMKnAiIAIABBAEgbRVxyACACIAZBEGprQcKfAUpccgAgAiABNgIAIAJBBGohAgsgBkHCnAJqIAZBEGogAiAEECAgBkHCrAJqIAZBwqgCahAORVxyASAEIAQoAgBBAnI2AgAMAQsgBCAEKAIAQQZyNgIAIAVCADcDAAsgBigCwqwCIAZBwpwCahAMGiAGQcKwAmokAAvClQsCCX8CfiMAQcKgAmsiBiQAIAYgAjYCwpgCIAYgATYCwpwCIAMQLiEAIAYgAygCHCIBNgIAIAFBw6zClwFHBEAgASABKAIEQQFqNgIECyAGQcOkwpkBEFxyIQECQCAGKAIAIgJBw6zClwFGXHIAIAIgAigCBCJcbkEBazYCBCBcblxyACACIAIoAgAoAggRAQALIAEgASgCACgCEBEAACFcbiAGQcKMAmogASABKAIAKAIUEQMAIAMgBkHCoAFqEFQhAwJAIAZBwpwCaiAGQcKYAmoQDkUEQCAGIQIDQCACIAZrQcKfAUohCQJAA0AgBigCwpACIAYsAMKXAiIBIAFBAEgbRVxyAQJ/IAYoAsKcAiIBKAIMIgcgASgCEEYEQCABIAEoAgAoAiQRAAAMAQsgBygCAAsgXG5HXHIBIAYoAsKcAhASGiAJXHIACyACQQA2AgAgAkEEaiECDAELCwJ/IAYoAsKcAiIBKAIMIgkgASgCEEYEQCABIAEoAgAoAiQRAAAMAQsgCSgCAAshASADKAJkIQkCfyADKAJgIgcgAUcEQEEAIAEgCUdccgEaCyAGKALCnAIQEhogASAJRiABIAdHcgshCSAGQcKcAmogBkHCmAJqEA4EQCAEIAQoAgBBBnI2AgAgBUEANgIADAILQRAhAQJAAkAgAEEQRwRAIAAEQCAAIQEMAwsCfyAGKALCnAIiACgCDCIHIAAoAhBGBEAgACAAKAIAKAIkEQAADAELIAcoAgALIAMoAgBHBEBBXG4hAQwDCyAGKALCnAIQEhogBkHCnAJqIAZBwpgCahAORQRAAn8gBigCwpwCIgAoAgwiByAAKAIQRgRAIAAgACgCACgCJBEAAAwBCyAHKAIACyIAIAMoAlhGXHICIAAgAygCXFxGXHICQQEhDEEIIQEMAwsgBCAEKAIAQQJyNgIAIAVBADYCAAwECwJ/IAYoAsKcAiIAKAIMIgcgACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgBygCAAsgAygCAEdccgEgBigCwpwCEBIaIAZBwpwCaiAGQcKYAmoQDgRAIAQgBCgCAEECcjYCACAFQQA2AgAMBAsCfyAGKALCnAIiACgCDCIHIAAoAhBGBEAgACAAKAIAKAIkEQAADAELIAcoAgALIgAgAygCWEZccgAgACADKAJcXEZccgBBASEMDAELIAYoAsKcAhASGgsgAUEQRiEHA0ACQCAGQcKcAmogBkHCmAJqEA5ccgACQAJAAn8gBigCwpwCIgAoAgwiXHIgACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgXHIoAgALIgAgXG5HXHIAIAYoAsKQAiAGLADClwIiXHIgXHJBAEgbRVxyACACIAZrQcKfAUpccgEgAiALNgIAIAJBBGohAkEAIQsMAQsgAyAAEFMiAEEVSlxyASAAQQZrIAAgAEEPShsgACAHGyIAIAFOXHIBIAHCrSAIwq1+Ig/CpyEIQQEhDAJAIA9CIMKIQgBSBEBBASEADAELIADCrCAIwq18Ig9CH8KGQh/ChyIQIA9SIBBCAFNyIQAgD8KnIQgLIAtBAWohCyAAIA5BAXFyIQ4LIAYoAsKcAhASGgwBCwsCQCAMRQRAIAQgBCgCAEEEcjYCAEEAIQgMAQsgDkEBcQRAIAQgBCgCAEEEcjYCAEHCgMKAwoDCgHhBw7/Dv8O/w78HIAkbIQgMAQsgCUUEQCAIQQBOXHIBIAQgBCgCAEEEcjYCAEHDv8O/w7/DvwchCAwBCyAIQcKBwoDCgMKAeE8EQCAEIAQoAgBBBHI2AgBBwoDCgMKAwoB4IQgMAQtBACAIayEICyAFIAg2AgACQCAGKALCkAIgBiwAwpcCIgAgAEEASBtFXHIAIAIgBmtBwp8BSlxyACACIAs2AgAgAkEEaiECCyAGQcKMAmogBiACIAQQICAGQcKcAmogBkHCmAJqEA5FXHIBIAQgBCgCAEECcjYCAAwBCyAEIAQoAgBBBnI2AgAgBUEANgIACyAGKALCnAIgBkHCjAJqEAwaIAZBwqACaiQAC8KWAwECfyMAQSBrIgYkACAGIAE2AhwCQCADLQAEQQFxRQRAIAZBfzYCACAAIAEgAiADIAQgBiAAKAIAKAIQEQUAIQECQAJAAkAgBigCAA4CAAECCyAFQQA6AAAMAwsgBUEBOgAADAILIAVBAToAACAEQQQ2AgAMAQsgBiADKAIcIgA2AgAgAEHDrMKXAUcEQCAAIAAoAgRBAWo2AgQLIAZBwpzCmQEQXHIhBwJAIAYoAgAiAEHDrMKXAUZccgAgACAAKAIEIgFBAWs2AgQgAVxyACAAIAAoAgAoAggRAQALIAYgAygCHCIANgIAIABBw6zClwFHBEAgACAAKAIEQQFqNgIECyAGQcOkwpkBEFxyIQACQCAGKAIAIgFBw6zClwFGXHIAIAEgASgCBCIDQQFrNgIEIANccgAgASABKAIAKAIIEQEACyAGIAAgACgCACgCGBEDACAGQQxyIAAgACgCACgCHBEDACAFIAZBHGogAiAGIAZBGGoiAyAHIARBARBsIAZGOgAAIAYoAhwhAQNAIANBDGsQDCIDIAZHXHIACwsgBkEgaiQAIAELSQECfyMAQRBrIgYkACADIAMoAgQiB0HCtcO/fnFBCHI2AgQgASACIAMgBCAGQQxqEMO5ASADIAc2AgQgBSAGKAIMNgIAIAZBEGokAAvDowUCAn8BfgJ/IwBBwqACayIAJAAgACACNgLCmAIgACABNgLCnAIgAEHDoAFqIAMgAEHDsAFqIABBw68BaiAAQcOuAWoQwpcBIABBADYCw5gBIABCADcDw5ABIABBw5ABaiIBQVxuEB4gACAAKALDkAEgASAALADDmwFBAEgbIgE2AsOMASAAIABBIGo2AhwgAEEANgIYIABBAToAFyAAQcOFADoAFkEAIQIDQAJAAkACQCAAQcKcAmogAEHCmAJqEA9ccgAgACgCw4wBIAEgACgCw5QBIAAsAMObASIDIANBAEgbIgNqRgRAIABBw5ABaiIBIANBAXQQHiABQVxuIAAoAsOYAUHDv8O/w7/DvwdxQQFrIAAsAMObAUEAThsQHiAAIAAoAsOQASABIAAsAMObAUEASBsiASADajYCw4wBCwJ/IAAoAsKcAiIDKAIMIgYgAygCEEYEQCADIAMoAgAoAiQRAAAMAQsgBi0AAAvDgCAAQRdqIABBFmogASAAQcOMAWogACwAw68BIAAsAMOuASAAQcOgAWogAEEgaiAAQRxqIABBGGogAEHDsAFqEMKWAVxyACACXHIBQQAhAiAAKALDjAEgAWsiBkEATFxyAgJAAkAgAS0AACIDQStrIgcOAwEAAQALIANBLkZccgJBASECIANBMGtBw78BcUFcbklccgMMAQsgBkEBRlxyAgJAIAcOAwADAAMLIAEtAAEiA0EuRlxyAUEBIQIgA0Ewa0HDvwFxQQlNXHICCwJAIAAoAsOkASAALADDqwEiAiACQQBIG0VccgAgAC0AF0EBcUVccgAgACgCHCICIABBIGprQcKfAUpccgAgACACQQRqNgIcIAIgACgCGDYCAAsgACABIAAoAsOMASAEEMO1ASAAKQMAIQggBSAAKQMINwMIIAUgCDcDACAAQcOgAWogAEEgaiAAKAIcIAQQICAAQcKcAmogAEHCmAJqEA8EQCAEIAQoAgBBAnI2AgALIAAoAsKcAiAAQcOQAWoQDBogAEHDoAFqEAwaIABBwqACaiQADAMLQQEhAgsgACgCwpwCEBMaDAALAAsLw4wFAQJ/An8jAEHCkAJrIgAkACAAIAI2AsKIAiAAIAE2AsKMAiAAQcOQAWogAyAAQcOgAWogAEHDnwFqIABBw54BahDClwEgAEEANgLDiAEgAEIANwPDgAEgAEHDgAFqIgFBXG4QHiAAIAAoAsOAASABIAAsAMOLAUEASBsiATYCwrwBIAAgAEEQajYCDCAAQQA2AgggAEEBOgAHIABBw4UAOgAGQQAhAgNAAkACQAJAIABBwowCaiAAQcKIAmoQD1xyACAAKALCvAEgASAAKALDhAEgACwAw4sBIgMgA0EASBsiA2pGBEAgAEHDgAFqIgEgA0EBdBAeIAFBXG4gACgCw4gBQcO/w7/Dv8O/B3FBAWsgACwAw4sBQQBOGxAeIAAgACgCw4ABIAEgACwAw4sBQQBIGyIBIANqNgLCvAELAn8gACgCwowCIgMoAgwiBiADKAIQRgRAIAMgAygCACgCJBEAAAwBCyAGLQAAC8OAIABBB2ogAEEGaiABIABBwrwBaiAALADDnwEgACwAw54BIABBw5ABaiAAQRBqIABBDGogAEEIaiAAQcOgAWoQwpYBXHIAIAJccgFBACECIAAoAsK8ASABayIGQQBMXHICAkACQCABLQAAIgNBK2siBw4DAQABAAsgA0EuRlxyAkEBIQIgA0Ewa0HDvwFxQVxuSVxyAwwBCyAGQQFGXHICAkAgBw4DAAMAAwsgAS0AASIDQS5GXHIBQQEhAiADQTBrQcO/AXFBCU1ccgILAkAgACgCw5QBIAAsAMObASICIAJBAEgbRVxyACAALQAHQQFxRVxyACAAKAIMIgIgAEEQamtBwp8BSlxyACAAIAJBBGo2AgwgAiAAKAIINgIACyAFIAEgACgCwrwBIAQQw7YBOQMAIABBw5ABaiAAQRBqIAAoAgwgBBAgIABBwowCaiAAQcKIAmoQDwRAIAQgBCgCAEECcjYCAAsgACgCwowCIABBw4ABahAMGiAAQcOQAWoQDBogAEHCkAJqJAAMAwtBASECCyAAKALCjAIQExoMAAsACwvDjAUBAn8CfyMAQcKQAmsiACQAIAAgAjYCwogCIAAgATYCwowCIABBw5ABaiADIABBw6ABaiAAQcOfAWogAEHDngFqEMKXASAAQQA2AsOIASAAQgA3A8OAASAAQcOAAWoiAUFcbhAeIAAgACgCw4ABIAEgACwAw4sBQQBIGyIBNgLCvAEgACAAQRBqNgIMIABBADYCCCAAQQE6AAcgAEHDhQA6AAZBACECA0ACQAJAAkAgAEHCjAJqIABBwogCahAPXHIAIAAoAsK8ASABIAAoAsOEASAALADDiwEiAyADQQBIGyIDakYEQCAAQcOAAWoiASADQQF0EB4gAUFcbiAAKALDiAFBw7/Dv8O/w78HcUEBayAALADDiwFBAE4bEB4gACAAKALDgAEgASAALADDiwFBAEgbIgEgA2o2AsK8AQsCfyAAKALCjAIiAygCDCIGIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIAYtAAALw4AgAEEHaiAAQQZqIAEgAEHCvAFqIAAsAMOfASAALADDngEgAEHDkAFqIABBEGogAEEMaiAAQQhqIABBw6ABahDClgFccgAgAlxyAUEAIQIgACgCwrwBIAFrIgZBAExccgICQAJAIAEtAAAiA0ErayIHDgMBAAEACyADQS5GXHICQQEhAiADQTBrQcO/AXFBXG5JXHIDDAELIAZBAUZccgICQCAHDgMAAwADCyABLQABIgNBLkZccgFBASECIANBMGtBw78BcUEJTVxyAgsCQCAAKALDlAEgACwAw5sBIgIgAkEASBtFXHIAIAAtAAdBAXFFXHIAIAAoAgwiAiAAQRBqa0HCnwFKXHIAIAAgAkEEajYCDCACIAAoAgg2AgALIAUgASAAKALCvAEgBBDDuAE4AgAgAEHDkAFqIABBEGogACgCDCAEECAgAEHCjAJqIABBwogCahAPBEAgBCAEKAIAQQJyNgIACyAAKALCjAIgAEHDgAFqEAwaIABBw5ABahAMGiAAQcKQAmokAAwDC0EBIQILIAAoAsKMAhATGgwACwALC8KuXG4CB38EfiMAQcOQAWsiBiQAIAYgAjYCw4gBIAYgATYCw4wBIAMQLiEBIAZBEGoiAiADKAIcIgA2AgAgAEHDrMKXAUcEQCAAIAAoAgRBAWo2AgQLIAJBw5zCmQEQXHIhAAJAIAYoAhAiA0HDrMKXAUZccgAgAyADKAIEIgdBAWs2AgQgB1xyACADIAMoAgAoAggRAQALIAAgACgCACgCEBEAACEHIAZBwrwBaiAAIAAoAgAoAhQRAwACQCAGQcOMAWogBkHDiAFqEA9FBEADQCACIAZBEGprQcKfAUohAwJAA0AgBigCw4ABIAYsAMOHASIAIABBAEgbRVxyASAHQcO/AXECfyAGKALDjAEiACgCDCIJIAAoAhBGBEAgACAAKAIAKAIkEQAADAELIAktAAALQcO/AXFHXHIBIAYoAsOMARATGiADXHIACyACQQA2AgAgAkEEaiECDAELCwJAAkACfyAGKALDjAEiACgCDCIDIAAoAhBGBEAgACAAKAIAKAIkEQAADAELIAMtAAALQcO/AXEiAEEraw4DAAEAAQsgBigCw4wBEBMaIABBLUYhDAsgBkHDjAFqIAZBw4gBahAPBEAgBCAEKAIAQQZyNgIAIAVCADcDAAwCC0EQIQACQAJAIAFBEEcEQCABBEAgASEADAMLAn8gBigCw4wBIgEoAgwiAyABKAIQRgRAIAEgASgCACgCJBEAAAwBCyADLQAAC0HDvwFxQTBHBEBBXG4hAAwDCyAGKALDjAEQExogBkHDjAFqIAZBw4gBahAPRQRAAn8gBigCw4wBIgEoAgwiAyABKAIQRgRAIAEgASgCACgCJBEAAAwBCyADLQAAC0EgckHDvwFxQcO4AEZccgJBASEIQQghAAwDCyAEIAQoAgBBAnI2AgAgBUIANwMADAQLAn8gBigCw4wBIgEoAgwiAyABKAIQRgRAIAEgASgCACgCJBEAAAwBCyADLQAAC0HDvwFxQTBHXHIBIAYoAsOMARATGiAGQcOMAWogBkHDiAFqEA8EQCAEIAQoAgBBAnI2AgAgBUIANwMADAQLAn8gBigCw4wBIgEoAgwiAyABKAIQRgRAIAEgASgCACgCJBEAAAwBCyADLQAAC0EgckHDvwFxQcO4AEZccgBBASEIDAELIAYoAsOMARATGgsgAMKtIQ8gAEEQRiEJQQAhAQNAAkAgBkHDjAFqIAZBw4gBahAPXHIAAkACQCAHQcO/AXECfyAGKALDjAEiAygCDCJcbiADKAIQRgRAIAMgAygCACgCJBEAAAwBCyBcbi0AAAsiA0HDvwFxR1xyACAGKALDgAEgBiwAw4cBIlxuIFxuQQBIG0VccgAgAiAGQRBqa0HCnwFKXHIBIAIgATYCACACQQRqIQJBACEBDAELIAPDgBBVIgNBFUpccgEgA0EGayADIANBD0obIAMgCRsiAyAATlxyASAGIA9CACBcckIAEBhBASEIIAYpAwAhXHIgAUEBaiEBIAYpAwhCAFIEf0EBBUIAIFxyIFxyIAPCrCIOfCJcclbCrSAOQj/Ch3wiDkIBwoN9IhAgDsKFQgBSIBBCAFNyCyALQQFxciELCyAGKALDjAEQExoMAQsLIAUgCEF/cyALckEBcQR+IAQgBCgCAEEEcjYCAEIAIAjCrX0FQgAgXHJ9IFxyIAwbCzcDAAJAIAYoAsOAASAGLADDhwEiACAAQQBIG0VccgAgAiAGQRBqa0HCnwFKXHIAIAIgATYCACACQQRqIQILIAZBwrwBaiAGQRBqIAIgBBAgIAZBw4wBaiAGQcOIAWoQD0VccgEgBCAEKAIAQQJyNgIADAELIAQgBCgCAEEGcjYCACAFQgA3AwALIAYoAsOMASAGQcK8AWoQDBogBkHDkAFqJAALw7IJAQh/IwBBw4ABayIAJAAgACACNgLCuAEgACABNgLCvAEgAxAuIQYgACADKAIcIgE2AgAgAUHDrMKXAUcEQCABIAEoAgRBAWo2AgQLIABBw5zCmQEQXHIhAQJAIAAoAgAiAkHDrMKXAUZccgAgAiACKAIEIgNBAWs2AgQgA1xyACACIAIoAgAoAggRAQALIAEgASgCACgCEBEAACELIABBwqwBaiABIAEoAgAoAhQRAwACQCAAQcK8AWogAEHCuAFqEA9FBEAgACEBA0AgASAAa0HCnwFKIQMCQANAIAAoAsKwASAALADCtwEiAiACQQBIG0VccgEgC0HDvwFxAn8gACgCwrwBIgIoAgwiCSACKAIQRgRAIAIgAigCACgCJBEAAAwBCyAJLQAAC0HDvwFxR1xyASAAKALCvAEQExogA1xyAAsgAUEANgIAIAFBBGohAQwBCwsCQAJAAn8gACgCwrwBIgIoAgwiAyACKAIQRgRAIAIgAigCACgCJBEAAAwBCyADLQAAC0HDvwFxIgJBK2sOAwABAAELIAAoAsK8ARATGiACQS1GIVxyCyAAQcK8AWogAEHCuAFqEA8EQCAEIAQoAgBBBnI2AgAgBUEAOwEADAILQRAhAgJAAkAgBkEQRwRAIAYEQCAGIQIMAwsCfyAAKALCvAEiAygCDCIGIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIAYtAAALQcO/AXFBMEcEQEFcbiECDAMLIAAoAsK8ARATGiAAQcK8AWogAEHCuAFqEA9FBEACfyAAKALCvAEiAygCDCIGIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIAYtAAALQSByQcO/AXFBw7gARlxyAkEBIQdBCCECDAMLIAQgBCgCAEECcjYCACAFQQA7AQAMBAsCfyAAKALCvAEiAygCDCIGIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIAYtAAALQcO/AXFBMEdccgEgACgCwrwBEBMaIABBwrwBaiAAQcK4AWoQDwRAIAQgBCgCAEECcjYCACAFQQA7AQAMBAsCfyAAKALCvAEiAygCDCIGIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIAYtAAALQSByQcO/AXFBw7gARlxyAEEBIQcMAQsgACgCwrwBEBMaCyACQRBGIQlBACEDA0ACQCAAQcK8AWogAEHCuAFqEA9ccgACQAJAIAtBw78BcQJ/IAAoAsK8ASIGKAIMIgggBigCEEYEQCAGIAYoAgAoAiQRAAAMAQsgCC0AAAsiBkHDvwFxR1xyACAAKALCsAEgACwAwrcBIgggCEEASBtFXHIAIAEgAGtBwp8BSlxyASABIAM2AgAgAUEEaiEBQQAhAwwBCyAGw4AQVSIGQRVKXHIBIAZBBmsgBiAGQQ9KGyAGIAkbIgggAk5ccgEgAiBcbkHDv8O/A3FsIgYgBiAIaiIHIAZBw7/DvwNLGyFcbiAMIAYgB3JBw7/DvwNLciEMQQEhByADQQFqIQMLIAAoAsK8ARATGgwBCwsgBSAHQX9zIAxyQQFxBH8gBCAEKAIAQQRyNgIAQQAgB2sFQQAgXG5rIFxuIFxyGws7AQACQCAAKALCsAEgACwAwrcBIgIgAkEASBtFXHIAIAEgAGtBwp8BSlxyACABIAM2AgAgAUEEaiEBCyAAQcKsAWogACABIAQQICAAQcK8AWogAEHCuAFqEA9FXHIBIAQgBCgCAEECcjYCAAwBCyAEIAQoAgBBBnI2AgAgBUEAOwEACyAAKALCvAEgAEHCrAFqEAwaIABBw4ABaiQAC8KvCwIHfwR+IwBBw5ABayIGJAAgBiACNgLDiAEgBiABNgLDjAEgAxAuIQEgBkEQaiICIAMoAhwiADYCACAAQcOswpcBRwRAIAAgACgCBEEBajYCBAsgAkHDnMKZARBcciEAAkAgBigCECIDQcOswpcBRlxyACADIAMoAgQiB0EBazYCBCAHXHIAIAMgAygCACgCCBEBAAsgACAAKAIAKAIQEQAAIQcgBkHCvAFqIAAgACgCACgCFBEDAAJAIAZBw4wBaiAGQcOIAWoQD0UEQANAIAIgBkEQamtBwp8BSiEDAkADQCAGKALDgAEgBiwAw4cBIgAgAEEASBtFXHIBIAdBw78BcQJ/IAYoAsOMASIAKAIMIgggACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgCC0AAAtBw78BcUdccgEgBigCw4wBEBMaIANccgALIAJBADYCACACQQRqIQIMAQsLAkACQAJ/IAYoAsOMASIAKAIMIgMgACgCEEYEQCAAIAAoAgAoAiQRAAAMAQsgAy0AAAtBw78BcSIAQStrDgMAAQABCyAGKALDjAEQExogAEEtRiELCyAGQcOMAWogBkHDiAFqEA8EQCAEIAQoAgBBBnI2AgAgBUIANwMADAILQRAhAAJAAkAgAUEQRwRAIAEEQCABIQAMAwsCfyAGKALDjAEiASgCDCIDIAEoAhBGBEAgASABKAIAKAIkEQAADAELIAMtAAALQcO/AXFBMEcEQEFcbiEADAMLIAYoAsOMARATGiAGQcOMAWogBkHDiAFqEA9FBEACfyAGKALDjAEiASgCDCIDIAEoAhBGBEAgASABKAIAKAIkEQAADAELIAMtAAALQSByQcO/AXFBw7gARlxyAkEBIQlBCCEADAMLIAQgBCgCAEECcjYCACAFQgA3AwAMBAsCfyAGKALDjAEiASgCDCIDIAEoAhBGBEAgASABKAIAKAIkEQAADAELIAMtAAALQcO/AXFBMEdccgEgBigCw4wBEBMaIAZBw4wBaiAGQcOIAWoQDwRAIAQgBCgCAEECcjYCACAFQgA3AwAMBAsCfyAGKALDjAEiASgCDCIDIAEoAhBGBEAgASABKAIAKAIkEQAADAELIAMtAAALQSByQcO/AXFBw7gARlxyAEEBIQkMAQsgBigCw4wBEBMaCyAAwq0hDyAAQRBGIQhBACEBA0ACQCAGQcOMAWogBkHDiAFqEA9ccgACQAJAIAdBw78BcQJ/IAYoAsOMASIDKAIMIlxuIAMoAhBGBEAgAyADKAIAKAIkEQAADAELIFxuLQAACyIDQcO/AXFHXHIAIAYoAsOAASAGLADDhwEiXG4gXG5BAEgbRVxyACACIAZBEGprQcKfAUpccgEgAiABNgIAIAJBBGohAkEAIQEMAQsgA8OAEFUiA0EVSlxyASADQQZrIAMgA0EPShsgAyAIGyIDIABOXHIBIAYgD0IAIFxyQgAQGEEBIQkgBikDACFcciABQQFqIQEgBikDCEIAUgR/QQEFQgAgXHIgXHIgA8KsIg58IlxyVsKtIA5CP8KHfCIOQgHCg30iECAOwoVCAFIgEEIAU3ILIAxBAXFyIQwLIAYoAsOMARATGgwBCwsCQCAJRQRAIAQgBCgCAEEEcjYCAEIAIVxyDAELIAxBAXEEQCAEIAQoAgBBBHI2AgBCwoDCgMKAwoDCgMKAwoDCgMKAf0LDv8O/w7/Dv8O/w7/Dv8O/w78AIAsbIVxyDAELIAtFBEAgXHJCAFlccgEgBCAEKAIAQQRyNgIAQsO/w7/Dv8O/w7/Dv8O/w7/DvwAhXHIMAQsgXHJCwoHCgMKAwoDCgMKAwoDCgMKAf1oEQCAEIAQoAgBBBHI2AgBCwoDCgMKAwoDCgMKAwoDCgMKAfyFccgwBC0IAIFxyfSFccgsgBSBccjcDAAJAIAYoAsOAASAGLADDhwEiACAAQQBIG0VccgAgAiAGQRBqa0HCnwFKXHIAIAIgATYCACACQQRqIQILIAZBwrwBaiAGQRBqIAIgBBAgIAZBw4wBaiAGQcOIAWoQD0VccgEgBCAEKAIAQQJyNgIADAELIAQgBCgCAEEGcjYCACAFQgA3AwALIAYoAsOMASAGQcK8AWoQDBogBkHDkAFqJAALw7xcbgIIfwJ+IwBBw4ABayIAJAAgACACNgLCuAEgACABNgLCvAEgAxAuIQYgACADKAIcIgE2AgAgAUHDrMKXAUcEQCABIAEoAgRBAWo2AgQLIABBw5zCmQEQXHIhAQJAIAAoAgAiAkHDrMKXAUZccgAgAiACKAIEIgNBAWs2AgQgA1xyACACIAIoAgAoAggRAQALIAEgASgCACgCEBEAACELIABBwqwBaiABIAEoAgAoAhQRAwACQCAAQcK8AWogAEHCuAFqEA9FBEAgACEBA0AgASAAa0HCnwFKIQMCQANAIAAoAsKwASAALADCtwEiAiACQQBIG0VccgEgC0HDvwFxAn8gACgCwrwBIgIoAgwiCCACKAIQRgRAIAIgAigCACgCJBEAAAwBCyAILQAAC0HDvwFxR1xyASAAKALCvAEQExogA1xyAAsgAUEANgIAIAFBBGohAQwBCwsCQAJAAn8gACgCwrwBIgIoAgwiAyACKAIQRgRAIAIgAigCACgCJBEAAAwBCyADLQAAC0HDvwFxIgJBK2sOAwABAAELIAAoAsK8ARATGiACQS1GIQwLIABBwrwBaiAAQcK4AWoQDwRAIAQgBCgCAEEGcjYCACAFQQA2AgAMAgtBECECAkACQCAGQRBHBEAgBgRAIAYhAgwDCwJ/IAAoAsK8ASIDKAIMIgYgAygCEEYEQCADIAMoAgAoAiQRAAAMAQsgBi0AAAtBw78BcUEwRwRAQVxuIQIMAwsgACgCwrwBEBMaIABBwrwBaiAAQcK4AWoQD0UEQAJ/IAAoAsK8ASIDKAIMIgYgAygCEEYEQCADIAMoAgAoAiQRAAAMAQsgBi0AAAtBIHJBw78BcUHDuABGXHICQQEhCUEIIQIMAwsgBCAEKAIAQQJyNgIAIAVBADYCAAwECwJ/IAAoAsK8ASIDKAIMIgYgAygCEEYEQCADIAMoAgAoAiQRAAAMAQsgBi0AAAtBw78BcUEwR1xyASAAKALCvAEQExogAEHCvAFqIABBwrgBahAPBEAgBCAEKAIAQQJyNgIAIAVBADYCAAwECwJ/IAAoAsK8ASIDKAIMIgYgAygCEEYEQCADIAMoAgAoAiQRAAAMAQsgBi0AAAtBIHJBw78BcUHDuABGXHIAQQEhCQwBCyAAKALCvAEQExoLIAJBEEYhCEEAIQMDQAJAIABBwrwBaiAAQcK4AWoQD1xyAAJAAkAgC0HDvwFxAn8gACgCwrwBIgYoAgwiXG4gBigCEEYEQCAGIAYoAgAoAiQRAAAMAQsgXG4tAAALIgZBw78BcUdccgAgACgCwrABIAAsAMK3ASJcbiBcbkEASBtFXHIAIAEgAGtBwp8BSlxyASABIAc2AgAgAUEEaiEBQQAhBwwBCyAGw4AQVSIGQRVKXHIBIAZBBmsgBiAGQQ9KGyAGIAgbIgYgAk5ccgEgAsKtIAPCrX4iDsKnIQNBASEJAkAgDkIgwohCAFIEQEEBIQYMAQsgBsKsIAPCrXwiDkIfwoZCH8KHIg8gDlIgD0IAU3IhBiAOwqchAwsgB0EBaiEHIAYgXHJBAXFyIVxyCyAAKALCvAEQExoMAQsLAkAgCUUEQCAEIAQoAgBBBHI2AgBBACEDDAELIFxyQQFxBEAgBCAEKAIAQQRyNgIAQcKAwoDCgMKAeEHDv8O/w7/DvwcgDBshAwwBCyAMRQRAIANBAE5ccgEgBCAEKAIAQQRyNgIAQcO/w7/Dv8O/ByEDDAELIANBwoHCgMKAwoB4TwRAIAQgBCgCAEEEcjYCAEHCgMKAwoDCgHghAwwBC0EAIANrIQMLIAUgAzYCAAJAIAAoAsKwASAALADCtwEiAiACQQBIG0VccgAgASAAa0HCnwFKXHIAIAEgBzYCACABQQRqIQELIABBwqwBaiAAIAEgBBAgIABBwrwBaiAAQcK4AWoQD0VccgEgBCAEKAIAQQJyNgIADAELIAQgBCgCAEEGcjYCACAFQQA2AgALIAAoAsK8ASAAQcKsAWoQDBogAEHDgAFqJAALwpYDAQJ/IwBBIGsiBiQAIAYgATYCHAJAIAMtAARBAXFFBEAgBkF/NgIAIAAgASACIAMgBCAGIAAoAgAoAhARBQAhAQJAAkACQCAGKAIADgIAAQILIAVBADoAAAwDCyAFQQE6AAAMAgsgBUEBOgAAIARBBDYCAAwBCyAGIAMoAhwiADYCACAAQcOswpcBRwRAIAAgACgCBEEBajYCBAsgBkHCpMKZARBcciEHAkAgBigCACIAQcOswpcBRlxyACAAIAAoAgQiAUEBazYCBCABXHIAIAAgACgCACgCCBEBAAsgBiADKAIcIgA2AgAgAEHDrMKXAUcEQCAAIAAoAgRBAWo2AgQLIAZBw5zCmQEQXHIhAAJAIAYoAgAiAUHDrMKXAUZccgAgASABKAIEIgNBAWs2AgQgA1xyACABIAEoAgAoAggRAQALIAYgACAAKAIAKAIYEQMAIAZBDHIgACAAKAIAKAIcEQMAIAUgBkEcaiACIAYgBkEYaiIDIAcgBEEBEG4gBkY6AAAgBigCHCEBA0AgA0EMaxAMIgMgBkdccgALCyAGQSBqJAAgAQtAAQF/QQAhAAN/IAEgAkYEfyAABSABKAIAIABBBHRqIgBBwoDCgMKAwoB/cSIDQRh2IANyIABzIQAgAUEEaiEBDAELCwsrACAAIAIgAWsiAkECdRBkIQAgAgRAIAAgASACw7xcbgAACyAAIAJqQQA2AgALCwAgACACIAMQw4sDC1QBAn8CQANAIAMgBEcEQEF/IQAgASACRlxyAiABKAIAIgUgAygCACIGSFxyAiAFIAZKBEBBAQ8FIANBBGohAyABQQRqIQEMAgsACwsgASACRyEACyAAC0ABAX9BACEAA38gASACRgR/IAAFIAEsAAAgAEEEdGoiAEHCgMKAwoDCgH9xIgNBGHYgA3IgAHMhACABQQFqIQEMAQsLCwsAIAAgAiADEMKQAgteAQN/IAEgBCADa2ohBQJAA0AgAyAERwRAQX8hACABIAJGXHICIAEsAAAiBiADLAAAIgdIXHICIAYgB0oEQEEBDwUgA0EBaiEDIAFBAWohAQwCCwALCyACIAVHIQALIAALwocIAQV/IAEoAgAhBAJAAkACQAJAAkACQAJAAn8CQAJAAkACQCADRVxyACADKAIAIgVFXHIAIABFBEAgAiEDDAMLIANBADYCACACIQMMAQsCQEHCrMO1ACgCACgCAEUEQCAARVxyASACRVxyDCACIQUDQCAELAAAIgMEQCAAIANBw7/CvwNxNgIAIABBBGohACAEQQFqIQQgBUEBayIFXHIBDA4LCyAAQQA2AgAgAUEANgIAIAIgBWsPCyACIQMgAEVccgMMBQsgBBAwDwtBASEHDAMLQQAMAQtBAQshBwNAIAdFBEAgBC0AAEEDdiIGQRBrIAVBGnUgBmpyQQdLXHIDAn8gBEEBaiIGIAVBwoDCgMKAEHFFXHIAGiAGLAAAQUBOBEAgBEEBayEEDAcLIARBAmoiBiAFQcKAwoAgcUVccgAaIAYsAABBQE4EQCAEQQFrIQQMBwsgBEEDagshBCADQQFrIQNBASEHDAELA0ACQCAELAAAIgVBAExccgAgBEEDcVxyACAEKAIAIgVBwoHCgsKECGsgBXJBwoDCgcKCwoR4cVxyAANAIANBBGshAyAEIgVBBGohBCAFKAIEIgVBwoHCgsKECGsgBXJBwoDCgcKCwoR4cUVccgALCyAFw4BBAEoEQCADQQFrIQMgBEEBaiEEDAELCyAFQcO/AXFBw4IBayIGQTJLXHIDIARBAWohBCAGQQJ0KALDsB4hBUEAIQcMAAsACwNAIAdFBEAgA0VccgcDQAJAIAQtAAAiB8OAIgVBAExccgACQCADQQVJXHIAIARBA3FccgACQANAIAQoAgAiBUHCgcKCwoQIayAFckHCgMKBwoLChHhxXHIBIAAgBUHDvwFxNgIAIAAgBC0AATYCBCAAIAQtAAI2AgggACAELQADNgIMIABBEGohACAEQQRqIQQgA0EEayIDQQRLXHIACyAELQAAIQULIAVBw78BcSEHIAXDgEEATFxyAQsgACAHNgIAIABBBGohACAEQQFqIQQgA0EBayIDXHIBDAkLCyAHQcOCAWsiBkEyS1xyAyAEQQFqIQQgBkECdCgCw7AeIQVBASEHDAELIAQtAAAiCEEDdiIGQRBrIAYgBUEadWpyQQdLXHIBAkACQAJ/IARBAWoiBiAIQcKAAWsgBUEGdHIiB0EATlxyABogBi0AAEHCgAFrIgZBP0tccgEgBiAHQQZ0IghyIQcgBEECaiIGIAhBAE5ccgAaIAYtAABBwoABayIGQT9LXHIBIAYgB0EGdHIhByAEQQNqCyEEIAAgBzYCACADQQFrIQMgAEEEaiEADAELQcOww7UAQRk2AgAgBEEBayEEDAULQQAhBwwACwALIARBAWshBCAFXHIBIAQtAAAhBQsgBUHDvwFxXHIAIAAEQCAAQQA2AgAgAUEANgIACyACIANrDwtBw7DDtQBBGTYCACAARVxyAQsgASAENgIAC0F/DwsgASAENgIAIAILWQEDfyAAKAJUIgNBACACQcKAAmoiBBBPIgUgA2sgBCAFGyIEIAIgAiAESxsiAgRAIAEgAyACw7xcbgAACyAAIAMgBGoiATYCVCAAIAE2AgggACACIANqNgIEIAILw6YDAgV/An4jAEEgayIEJAAgAULDv8O/w7/Dv8O/w78/woMhBwJAIAFCMMKIQsO/w78BwoMiCMKnIgNBwoHDvwBrQcO9AU0EQCAHQhnCiMKnIQICQCAAUCABQsO/w7/Dvw/CgyIHQsKAwoDCgAhUIAdCwoDCgMKACFEbRQRAIAJBAWohAgwBCyAAIAdCwoDCgMKACMKFwoRCAFJccgAgAkEBcSACaiECC0EAIAIgAkHDv8O/w78DSyIFGyECQcKBwoF/QcKAwoF/IAUbIANqIQMMAQsCQCAAIAfChFBccgAgCELDv8O/AVJccgAgB0IZwojCp0HCgMKAwoACciECQcO/ASEDDAELIANBw77CgAFLBEBBw78BIQMMAQtBwoDDvwBBwoHDvwAgCFAiBRsiBiADayICQcOwAEoEQEEAIQNBACECDAELIAcgB0LCgMKAwoDCgMKAwoDDgADChCAFGyEHQQAhBSADIAZHBEAgBEEQaiAAIAdBwoABIAJrEBwgBCkDECAEKQMYwoRCAFIhBQsgBCAAIAcgAhBDIAQpAwgiAEIZwojCpyECAkAgBCkDACAFwq3ChCIHUCAAQsO/w7/Dvw/CgyIAQsKAwoDCgAhUIABCwoDCgMKACFEbRQRAIAJBAWohAgwBCyAHIABCwoDCgMKACMKFwoRCAFJccgAgAkEBcSACaiECCyACQcKAwoDCgARzIAIgAkHDv8O/w78DSyIDGyECCyAEQSBqJAAgAUIgwojCp0HCgMKAwoDCgHhxIANBF3RyIAJywr4Lwr0yAxB/B34BfCMAQTBrIg4kAAJAAkAgAkECS1xyACACQQJ0KALClCshEiACLQDCkCshEQNAAn8gASgCBCICIAEoAmhHBEAgASACQQFqNgIEIAItAAAMAQsgARAZCyICQSBGIAJBCWtBBUlyXHIAC0EBIQYCQAJAIAJBK2sOAwABAAELQX9BASACQS1GGyEGIAEoAgQiAiABKAJoRwRAIAEgAkEBajYCBCACLQAAIQIMAQsgARAZIQILAkACQCACQV9xQcOJAEYEQANAIAhBB0ZccgICfyABKAIEIgIgASgCaEcEQCABIAJBAWo2AgQgAi0AAAwBCyABEBkLIQIgCCwAw58IIAhBAWohCCACQSByRlxyAAsLIAhBA0cEQCAIQQhGIgdccgEgA0VccgIgCEEESVxyAiAHXHIBCyABKQNwQgBTXHIAIAEgASgCBEEBazYCBCADRVxyACAIQQRJXHIAIAEgASgCBCAIa0EDajYCBAsjAEEQayIIJAAgBsKyQwAAwoB/wpTCvCIDQcO/w7/DvwNxIQYCfyADQRd2IgJBw78BcSIBBEAgAUHDvwFHBEAgBsKtQhnChiEUIAJBw78BcUHCgMO/AGoMAgsgBsKtQhnChiEUQcO/w78BDAELQQAgBkVccgAaIAggBsKtQgAgBmciAUHDkQBqEBwgCCkDCELCgMKAwoDCgMKAwoDDgADChSEUIAgpAwAhFUHCicO/ACABawshASAOIBU3AwAgDiABwq1CMMKGIANBH3bCrUI/wobChCAUwoQ3AwggCEEQaiQAIA4pAwghFCAOKQMAIRUMAgsCQAJAAkACQAJAAkAgCFxyAEEAIQggAkFfcUHDjgBHXHIAA0AgCEECRlxyAgJ/IAEoAgQiAiABKAJoRwRAIAEgAkEBajYCBCACLQAADAELIAEQGQshAiAILADCjQwgCEEBaiEIIAJBIHJGXHIACwsgCA4EAwEBAAELAkACfyABKAIEIgIgASgCaEcEQCABIAJBAWo2AgQgAi0AAAwBCyABEBkLQShGBEBBASEIQX8hBgwBC0LCgMKAwoDCgMKAwoDDoMO/w78AIRQgASkDcEIAU1xyBiABIAEoAgRBAWs2AgQMBgsDQAJ/IAEoAgQiAiABKAJoRwRAIAEgAkEBajYCBCACLQAADAELIAEQGQsiB0HDgQBrIQICQAJAIAdBMGtBXG5JXHIAIAJBGklccgAgB0HDnwBGXHIAIAdBw6EAa0EaT1xyAQsgBkEBayEGIAhBAWohCAwBCwtCwoDCgMKAwoDCgMKAw6DDv8O/ACEUIAdBKUZccgUgASkDcCIXQgBZBEAgASABKAIEQQFrNgIECyADBEAgCEVccgQgF0IAU1xyBCABIAEoAgQgBmo2AgQMBgsMAQsgASkDcEIAWQRAIAEgASgCBEEBazYCBAsLQcOww7UAQRw2AgAgAUIAEFYMAgsCQCACQTBHXHIAAn8gASgCBCIIIAEoAmhHBEAgASAIQQFqNgIEIAgtAAAMAQsgARAZC0FfcUHDmABGBEAjAEHCsANrIgUkAAJ/IAEoAgQiAiABKAJoRwRAIAEgAkEBajYCBCACLQAADAELIAEQGQshAgJAAn8DQCACQTBHBEACQCACQS5HXHIEIAEoAgQiAiABKAJoRlxyACABIAJBAWo2AgQgAi0AAAwDCwUgASgCBCICIAEoAmhHBH9BASFcciABIAJBAWo2AgQgAi0AAAVBASFcciABEBkLIQIMAQsLIAEQGQsiAkEwRwRAQQEhEAwBCwNAIBdCAX0hFwJ/IAEoAgQiAiABKAJoRwRAIAEgAkEBajYCBCACLQAADAELIAEQGQsiAkEwRlxyAAtBASEQQQEhXHILQsKAwoDCgMKAwoDCgMOAw78/IRUDQAJAIAIhCAJAAkAgAkEwayIJQVxuSVxyACACQS5HIgcgAkEgciIIQcOhAGtBBUtxXHICIAdccgAgEFxyAkEBIRAgFCEXDAELIAhBw5cAayAJIAJBOUobIQICQCAUQgdXBEAgAiBcbkEEdGohXG4MAQsgFEIcWARAIAVBMGogAhAlIAVBIGogGSAVQgBCwoDCgMKAwoDCgMKAw4DDvT8QFCAFQRBqIAUpAzAgBSkDOCAFKQMgIhkgBSkDKCIVEBQgBSAFKQMQIAUpAxggFiAYECMgBSkDCCEYIAUpAwAhFgwBCyACRVxyACALXHIAIAVBw5AAaiAZIBVCAELCgMKAwoDCgMKAwoDCgMO/PxAUIAVBQGsgBSkDUCAFKQNYIBYgGBAjQQEhCyAFKQNIIRggBSkDQCEWCyAUQgF8IRRBASFccgsgASgCBCICIAEoAmhHBH8gASACQQFqNgIEIAItAAAFIAEQGQshAgwBCwsCfiBcckUEQAJAAkAgASkDcEIAWQRAIAEgASgCBCICQQFrNgIEIANFXHIBIAEgAkECazYCBCAQRVxyAiABIAJBA2s2AgQMAgsgA1xyAQsgAUIAEFYLIAVBw6AAakQAAAAAAAAAACAGwrfCphAvIAUpA2AhFiAFKQNoDAELIBRCB1cEQCAUIRUDQCBcbkEEdCFcbiAVQgF8IhVCCFJccgALCwJAAkACQCACQV9xQcOQAEYEQCABIAMQw78BIhVCwoDCgMKAwoDCgMKAwoDCgMKAf1JccgMgAwRAIAEpA3BCAFlccgIMAwtCACEWIAFCABBWQgAMBAtCACEVIAEpA3BCAFNccgILIAEgASgCBEEBazYCBAtCACEVCyBcbkUEQCAFQcOwAGpEAAAAAAAAAAAgBsK3wqYQLyAFKQNwIRYgBSkDeAwBCyAXIBQgEBtCAsKGIBV8QiB9IhRBACASa8KtVQRAQcOww7UAQcOEADYCACAFQcKgAWogBhAlIAVBwpABaiAFKQPCoAEgBSkDwqgBQn9Cw7/Dv8O/w7/Dv8O/wr/Dv8O/ABAUIAVBwoABaiAFKQPCkAEgBSkDwpgBQn9Cw7/Dv8O/w7/Dv8O/wr/Dv8O/ABAUIAUpA8KAASEWIAUpA8KIAQwBCyASQcOiAWvCrCAUVwRAIFxuQQBOBEADQCAFQcKgA2ogFiAYQgBCwoDCgMKAwoDCgMKAw4DDv8K/fxAjIBYgGELCgMKAwoDCgMKAwoDCgMO/PxDCsgEhASAFQcKQA2ogFiAYIAUpA8KgAyAWIAFBAE4iAhsgBSkDwqgDIBggAhsQIyACIFxuQQF0IgFyIVxuIBRCAX0hFCAFKQPCmAMhGCAFKQPCkAMhFiABQQBOXHIACwsCfiAUQSAgEmvCrXwiFcKnIgFBACABQQBKGyARIBUgEcKtUxsiAUHDsQBPBEAgBUHCgANqIAYQJSAFKQPCiAMhFSAFKQPCgAMhGUIADAELIAVBw6ACakHCkAEgAWsQwp0BEC8gBUHDkAJqIAYQJSAFKQPDkAIhGSAFKQPDoAIhFyAFIAUpA8OoAkLDv8O/w7/Dv8O/w7/Dv8O/w78AwoMgBSkDw5gCIhVCwoDCgMKAwoDCgMKAwoDCgMKAf8KDwoQ3A8O4AiAFIBc3A8OwAiAFKQPDuAIhGiAFKQPDsAILIRcgBUHDgAJqIFxuIFxuQQFxRSAWIBhCAEIAEEFBAEcgAUEgSXFxIgFyEEogBUHCsAJqIBkgFSAFKQPDgAIgBSkDw4gCEBQgBUHCkAJqIAUpA8KwAiAFKQPCuAIgFyAaECMgBUHCoAJqIBkgFUIAIBYgARtCACAYIAEbEBQgBUHCgAJqIAUpA8KgAiAFKQPCqAIgBSkDwpACIAUpA8KYAhAjIAVBw7ABaiAFKQPCgAIgBSkDwogCIBcgGhDCnAEgBSkDw7ABIhcgBSkDw7gBIhVCAEIAEEFFBEBBw7DDtQBBw4QANgIACyAFQcOgAWogFyAVIBTCpxDCgwIgBSkDw6ABIRYgBSkDw6gBDAELQcOww7UAQcOEADYCACAFQcOQAWogBhAlIAVBw4ABaiAFKQPDkAEgBSkDw5gBQgBCwoDCgMKAwoDCgMKAw4AAEBQgBUHCsAFqIAUpA8OAASAFKQPDiAFCAELCgMKAwoDCgMKAwoDDgAAQFCAFKQPCsAEhFiAFKQPCuAELIRQgDiAWNwMQIA4gFDcDGCAFQcKwA2okACAOKQMYIRQgDikDECEVDAQLIAEpA3BCAFNccgAgASABKAIEQQFrNgIECyABIQkgAiEHIAYhCCADIQJBACEGIwBBwpDDhgBrIgQkAEEAIBJrIlxyIBFrIRMCQAJ/A0AgB0EwRwRAAkAgB0EuR1xyBCAJKAIEIgEgCSgCaEZccgAgCSABQQFqNgIEIAEtAAAMAwsFIAkoAgQiASAJKAJoRwR/QQEhDCAJIAFBAWo2AgQgAS0AAAVBASEMIAkQGQshBwwBCwsgCRAZCyIHQTBGBEADQCAUQgF9IRQCfyAJKAIEIgEgCSgCaEcEQCAJIAFBAWo2AgQgAS0AAAwBCyAJEBkLIgdBMEZccgALQQEhDAtBASEGCyAEQQA2AsKQBiAHQTBrIQEgDgJ+AkACQAJAAkACQAJAIAdBLkYiA1xyACABQQlNXHIADAELA0ACQCADQQFxBEAgBkUEQCAVIRRBASEGDAILIAxFIQMMBAsgFUIBfCEVIFxuQcO8D0wEQCAPIBXCpyAHQTBGGyEPIARBwpAGaiBcbkECdGoiAyALBH8gByADKAIAQVxubGpBMGsFIAELNgIAQQEhDEEAIAtBAWoiASABQQlGIgEbIQsgASBcbmohXG4MAQsgB0EwRlxyACAEIAQoAsKARkEBcjYCwoBGQcOcwo8BIQ8LAn8gCSgCBCIBIAkoAmhHBEAgCSABQQFqNgIEIAEtAAAMAQsgCRAZCyIHQTBrIQEgB0EuRiIDXHIAIAFBXG5JXHIACwsgFCAVIAYbIRQCQCAHQV9xQcOFAEdccgAgDEVccgACQCAJIAIQw78BIhdCwoDCgMKAwoDCgMKAwoDCgMKAf1JccgAgAkVccgRCACEXIAkpA3BCAFNccgAgCSAJKAIEQQFrNgIECyAUIBd8IRQMBAsgDEUhAyAHQQBIXHIBCyAJKQNwQgBTXHIAIAkgCSgCBEEBazYCBAsgA0VccgFBw7DDtQBBHDYCAAtCACEVIAlCABBWQgAMAQsgBCgCwpAGIgFFBEAgBEQAAAAAAAAAACAIwrfCphAvIAQpAwAhFSAEKQMIDAELAkAgFUIJVVxyACAUIBVSXHIAIBFBHk1BACABIBF2G1xyACAEQTBqIAgQJSAEQSBqIAEQSiAEQRBqIAQpAzAgBCkDOCAEKQMgIAQpAygQFCAEKQMQIRUgBCkDGAwBCyBcckEBdsKtIBRTBEBBw7DDtQBBw4QANgIAIARBw6AAaiAIECUgBEHDkABqIAQpA2AgBCkDaEJ/QsO/w7/Dv8O/w7/Dv8K/w7/DvwAQFCAEQUBrIAQpA1AgBCkDWEJ/QsO/w7/Dv8O/w7/Dv8K/w7/DvwAQFCAEKQNAIRUgBCkDSAwBCyASQcOiAWvCrCAUVQRAQcOww7UAQcOEADYCACAEQcKQAWogCBAlIARBwoABaiAEKQPCkAEgBCkDwpgBQgBCwoDCgMKAwoDCgMKAw4AAEBQgBEHDsABqIAQpA8KAASAEKQPCiAFCAELCgMKAwoDCgMKAwoDDgAAQFCAEKQNwIRUgBCkDeAwBCyALBEAgC0EITARAIARBwpAGaiBcbkECdGoiASgCACEGA0AgBkFcbmwhBiALQQFqIgtBCUdccgALIAEgBjYCAAsgXG5BAWohXG4LIBTCpyELAkAgD0EJTlxyACAUQhFVXHIAIAsgD0hccgAgFEIJUQRAIARBw4ABaiAIECUgBEHCsAFqIAQoAsKQBhBKIARBwqABaiAEKQPDgAEgBCkDw4gBIAQpA8KwASAEKQPCuAEQFCAEKQPCoAEhFSAEKQPCqAEMAgsgFEIIVwRAIARBwpACaiAIECUgBEHCgAJqIAQoAsKQBhBKIARBw7ABaiAEKQPCkAIgBCkDwpgCIAQpA8KAAiAEKQPCiAIQFCAEQcOgAWpBCCALa0ECdCgCw7AqECUgBEHDkAFqIAQpA8OwASAEKQPDuAEgBCkDw6ABIAQpA8OoARDCgQIgBCkDw5ABIRUgBCkDw5gBDAILIBEgC0F9bGpBG2oiAkEeTEEAIAQoAsKQBiIBIAJ2G1xyACAEQcOgAmogCBAlIARBw5ACaiABEEogBEHDgAJqIAQpA8OgAiAEKQPDqAIgBCkDw5ACIAQpA8OYAhAUIARBwrACaiALQQJ0QcOIKmooAgAQJSAEQcKgAmogBCkDw4ACIAQpA8OIAiAEKQPCsAIgBCkDwrgCEBQgBCkDwqACIRUgBCkDwqgCDAELA0AgXG4iAUEBayFcbiAEQcKQBmogAUECdGoiXHJBBGsoAgBFXHIAC0EAIQ8CQCALQQlvIgJFBEBBACEDDAELIAJBCWogAiAUQgBTGyEFAkAgAUUEQEEAIQNBACEBDAELQcKAwpTDq8OcA0EAIAVrQQJ0QcKQK2ooAgAiEG0hCUEAIQNBACEMQQAhBgNAIARBwpAGaiAGQQJ0aiICIAwgAigCACJcbiAQbiIHaiICNgIAIAtBCWsgCyACRSADIAZGcSICGyELIANBAWpBw78PcSADIAIbIQMgCSBcbiAHIBBsa2whDCAGQQFqIgYgAUdccgALIAxFXHIAIFxyIAw2AgAgAUEBaiEBCyALIAVrQQlqIQsLA0AgBEHCkAZqIANBAnRqIQkgC0EkSCEHAkADQCAHRQRAIAtBJEdccgIgCSgCAEHDkcOpw7kET1xyAgsgAUHDvw9qIVxuQQAhDANAIAEhAiAMwq0gBEHCkAZqIFxuQcO/D3EiXHJBAnRqIgE1AgBCHcKGfCIUQsKBwpTDq8OcA1QEf0EABSAUIBRCwoDClMOrw5wDwoAiFULCgMKUw6vDnAN+fSEUIBXCpwshDCABIBQ+AgAgAiACIAIgXHIgFEIAUhsgXHIgAkEBa0HDvw9xIgZHGyADIFxyRhshASBcckEBayFcbiADIFxyR1xyAAsgD0EdayEPIAIhASAMRVxyAAsgA0EBa0HDvw9xIgMgAUYEQCAEQcKQBmoiAiABQcO+D2pBw78PcUECdGoiASABKAIAIAZBAnQgAmooAgByNgIAIAYhAQsgC0EJaiELIARBwpAGaiADQQJ0aiAMNgIADAELCwJAA0AgAUEBakHDvw9xIQIgBEHCkAZqIAFBAWtBw78PcUECdGohBQNAQQlBASALQS1KGyEMAkADQEEAIQYCQANAAkAgAyAGakHDvw9xIgcgAUZccgAgBEHCkAZqIAdBAnRqKAIAIlxuIAZBAnQoAsOgKiIHSVxyACAHIFxuSVxyAiAGQQFqIgZBBEdccgELCyALQSRHXHIAQgAhFEEAIQZCACEVA0AgASADIAZqQcO/D3EiAkYEQCABQQFqQcO/D3EiAUECdCAEakEANgLCjAYLIARBwoAGaiAEQcKQBmogAkECdGooAgAQSiAEQcOwBWogFSAUQgBCwoDCgMKAwoDDpcKawrfCjsOAABAUIARBw6AFaiAEKQPDsAUgBCkDw7gFIAQpA8KABiAEKQPCiAYQIyAEKQPDqAUhFCAEKQPDoAUhFSAGQQFqIgZBBEdccgALIARBw5AFaiAIECUgBEHDgAVqIBUgFCAEKQPDkAUgBCkDw5gFEBRCACEUIAQpA8OIBSEXIAQpA8OABSEWIA9Bw7EAaiIHIBJrIlxuQQAgXG5BAEobIBEgXG4gEUgiBhsiCUHDsABNXHICQgAhFQwFCyAMIA9qIQ8gASADRlxyAAtBwoDClMOrw5wDIAx2IRBBfyAMdEF/cyFcckEAIQcgAyEGA0AgBEHCkAZqIgkgBkECdGoiXG4gByBcbigCACJcbiAMdmoiBzYCACALQQlrIAsgB0UgAyAGRnEiBxshCyADQQFqQcO/D3EgAyAHGyEDIFxuIFxycSAQbCEHIAZBAWpBw78PcSIGIAFHXHIACyAHRVxyASACIANHBEAgAUECdCAJaiAHNgIAIAIhAQwDCyAFIAUoAgBBAXI2AgAMAQsLCyAEQcKQBWpBw6EBIAlrEMKdARAvIAQpA8KQBSEUIAQgBCkDwpgFQsO/w7/Dv8O/w7/Dv8O/w7/DvwDCgyAXQsKAwoDCgMKAwoDCgMKAwoDCgH/Cg8KENwPCuAUgBCAUNwPCsAUgBCkDwrgFIRkgBCkDwrAFIRggBEHCgAVqQcOxACAJaxDCnQEQLyAEQcKgBWogFiAXIAQpA8KABSAEKQPCiAUQwoACIARBw7AEaiAWIBcgBCkDwqAFIhQgBCkDwqgFIhUQwpwBIARBw6AEaiAYIBkgBCkDw7AEIAQpA8O4BBAjIAQpA8OoBCEXIAQpA8OgBCEWCwJAIANBBGpBw78PcSICIAFGXHIAAkAgBEHCkAZqIAJBAnRqKAIAIgJBw7/DicK1w64BTQRAIAJFBEAgA0EFakHDvw9xIAFGXHICCyAEQcOwA2ogCMK3RAAAAAAAAMOQP8KiEC8gBEHDoANqIBQgFSAEKQPDsAMgBCkDw7gDECMgBCkDw6gDIRUgBCkDw6ADIRQMAQsgAkHCgMOKwrXDrgFHBEAgBEHDkARqIAjCt0QAAAAAAADDqD/CohAvIARBw4AEaiAUIBUgBCkDw5AEIAQpA8OYBBAjIAQpA8OIBCEVIAQpA8OABCEUDAELIAjCtyEbIAEgA0EFakHDvw9xRgRAIARBwpAEaiAbRAAAAAAAAMOgP8KiEC8gBEHCgARqIBQgFSAEKQPCkAQgBCkDwpgEECMgBCkDwogEIRUgBCkDwoAEIRQMAQsgBEHCsARqIBtEAAAAAAAAw6g/wqIQLyAEQcKgBGogFCAVIAQpA8KwBCAEKQPCuAQQIyAEKQPCqAQhFSAEKQPCoAQhFAsgCUHDrwBLXHIAIARBw5ADaiAUIBVCAELCgMKAwoDCgMKAwoDDgMO/PxDCgAIgBEHDgANqIBQgFUIAQsKAwoDCgMKAwoDCgMOAw78/ECMgFSAEKQPDiAMgBCkDw5ADIAQpA8OYA0IAQgAQQSIBGyEVIBQgBCkDw4ADIAEbIRQLIARBwrADaiAWIBcgFCAVECMgBEHCoANqIAQpA8KwAyAEKQPCuAMgGCAZEMKcASAEKQPCqAMhFyAEKQPCoAMhFgJAIBNBAmsgB0HDv8O/w7/DvwdxTlxyACAEIBdCw7/Dv8O/w7/Dv8O/w7/Dv8O/AMKDNwPCmAMgBCAWNwPCkAMgBEHCgANqIBYgF0IAQsKAwoDCgMKAwoDCgMKAw78/EBQgBCkDwpADIAQpA8KYA0LCgMKAwoDCgMKAwoDCgMK4w4AAEMKyASEDIAQpA8KIAyAXIANBAE4iAhshFyAEKQPCgAMgFiACGyEWIBQgFUIAQgAQQSEBIBMgAiAPaiIPQcOuAGpOBEAgBiAJIFxuRyADQQBIcnEgAUEAR3FFXHIBC0HDsMO1AEHDhAA2AgALIARBw7ACaiAWIBcgDxDCgwIgBCkDw7ACIRUgBCkDw7gCCzcDKCAOIBU3AyAgBEHCkMOGAGokACAOKQMoIRQgDikDICEVDAILDAELQgAhFAsgACAVNwMAIAAgFDcDCCAOQTBqJAALwrYDAgd/A34jAEEQayIIJAACQCAALQAAIgRFBEAgACEDDAELIAAhAwJAA0AgBMOAIgVBIEYgBUEJa0EFSXJFXHIBIAMtAAEhBCADQQFqIQMgBFxyAAsMAQsCQCAEQcO/AXEiBUEraw4DAAEAAQtBf0EAIAVBLUYbIQcgA0EBaiEDC0EAIQUDQAJAAkAgAy0AACIGQTBrIgRBw78BcUFcbklccgAgBkHDoQBrQcO/AXFBGU0EQCAGQcOXAGshBAwBCyAGQcOBAGtBw78BcUEZS1xyASAGQTdrIQQLIARBw78BcUFcbk9ccgAgCEJcbkIAIFxuQgAQGEEBIQYCQCAIKQMIQgBSXHIAIFxuQlxufiILIATCrULDvwHCgyIMQn/ChVZccgAgCyAMfCFcbkEBIQkgBSEGCyADQQFqIQMgBiEFDAELCyABBEAgASADIAAgCRs2AgALAkACQAJAIAUEQEHDsMO1AEHDhAA2AgAgB0EAIAJCAcKDUBshByACIVxuDAELIAIgXG5WXHIBCwJAIAdccgAgAsKnQQFxXHIAQcOww7UAQcOEADYCACACQgF9IQIMAgsgAiBcblpccgBBw7DDtQBBw4QANgIADAELIFxuIAfCrCICwoUgAn0hAgsgCEEQaiQAIAILwrQBAQV/IAAoAlQiAygCACEGIAMoAgQiBCAAKAIUIAAoAhwiB2siBSAEIAVJGyIFBEAgBQRAIAYgByAFw7xcbgAACyADIAMoAgAgBWoiBjYCACADIAMoAgQgBWsiBDYCBAsgBCACIAIgBEsbIgQEQCAEBEAgBiABIATDvFxuAAALIAMgAygCACAEaiIGNgIAIAMgAygCBCAEazYCBAsgBkEAOgAAIAAgACgCLCIBNgIcIAAgATYCFCACCykAIAEgASgCAEEHakF4cSIBQRBqNgIAIAAgASkDACABKQMIEMKFAjkDAAsJAxF/AXwDfgALwqIFAQZ/IwBBIGsiAyQAAkAgAUF/RgRAQQAhAQwBCyADIAE2AhQgAC0ALEEBRgRAQX8gASAAKAIgIQIjAEEQayIFJABBwqzDtQAoAgAiACEHIAIoAkhBAEwEQCACKALCiAFFBEAgAkHDkB5BwrgeIAAoAgAbNgLCiAELIAIoAkhFBEAgAkEBNgJICwtBwqzDtQAgAigCwogBNgIAAkACQAJAIAFBw78ATQRAAkAgASACKAJQRlxyACACKAIUIgAgAigCEEZccgAgAiAAQQFqNgIUIAAgAToAAAwECyMAQRBrIgQkACAEIAE6AA8CQAJAIAIoAhAiAAR/IAAFIAIQwqICBEBBfyEADAMLIAIoAhALIAIoAhQiBkZccgAgAUHDvwFxIgAgAigCUEZccgAgAiAGQQFqNgIUIAYgAToAAAwBCyACIARBD2pBASACKAIkEQQAQQFHBEBBfyEADAELIAQtAA8hAAsgBEEQaiQAIAAhAQwBCyACKAIQIAIoAhQiAEEEaksEQCAAIAEQwosCIgBBAEhccgIgAiACKAIUIABqNgIUDAELIAVBDGoiBCABEMKLAiIAQQBIXHIBIAQgACACEMKhAiAASVxyAQsgAUF/R1xyAQsgAiACKAIAQSByNgIAQX8hAQtBwqzDtQAgBzYCACAFQRBqJAAgAUF/RhshAQwBCyADIANBGGoiBTYCECADQSBqIQYgA0EUaiECA0ACQCAAKAIkIgQgACgCKCACIAUgA0EMaiADQRhqIAYgA0EQaiAEKAIAKAIMEQkAIQQgAygCDCACRlxyACAEQQNGBEAgAkEBQQEgACgCIBA+QQFGXHIDDAELIARBAUtccgAgA0EYaiICQQEgAygCECACayICIAAoAiAQPiACR1xyACADKAIMIQIgBEEBRlxyAQwCCwtBfyEBCyADQSBqJAAgAQtlAQF/AkAgAC0ALEUEQCACQQAgAkEAShshAgNAIAIgA0ZccgIgACABKAIAIAAoAgAoAjQRAgBBf0YEQCADDwUgAUEEaiEBIANBAWohAwwBCwALAAsgAUEEIAIgACgCIBA+IQILIAILMQAgACAAKAIAKAIYEQAAGiAAIAFBwrTCmQEQXHIiATYCJCAAIAEgASgCACgCHBEAADoALAvCqAIBBH8jAEEgayICJABBfyEDAkAgAUF/RgRAIAAtADRccgEgACAAKAIwIgNBf0c6ADQMAQsgAC0ANCEDAkACQCAALQA1QQFHXHIAIANBAXFFXHIAQX8hAyAAKAIwIAAoAiAQwo0CQX9GXHICDAELIANBAXFFXHIAIAIgACgCMDYCEEF/IQMCQAJAIAAoAiQiBCAAKAIoIAJBEGogAkEUaiIFIAJBDGogAkEYaiACQSBqIAUgBCgCACgCDBEJAEEBaw4DAwMAAQsgACgCMCEEIAIgAkEZajYCFCACIAQ6ABgLA0AgAigCFCIEIAJBGGpNXHIBIAIgBEEBayIENgIUIAQsAAAgACgCIBBEQX9HXHIACwwBCyAAQQE6ADQgACABNgIwIAEhAwsgAkEgaiQAIAMLCQAgAEEBEMKGAgsJACAAQQAQwoYCC0gAIAAgAUHCtMKZARBcciIBNgIkIAAgASABKAIAKAIYEQAANgIsIAAgACgCJCIBIAEoAgAoAhwRAAA6ADUgACgCLEEJTgRAECEACwvCnwIBBX8jAEEgayICJAACQCABQX9GBEBBACEBDAELIAIgAToAFyAALQAsQQFGBEAgAUF/IAAoAiAhAyMAQRBrIgAkACAAIAHDgDoADyAAQQ9qQQFBASADED4gAEEQaiQAQQFGGyEBDAELIAIgAkEYaiIFNgIQIAJBIGohBiACQRdqIQMDQAJAIAAoAiQiBCAAKAIoIAMgBSACQQxqIAJBGGogBiACQRBqIAQoAgAoAgwRCQAhBCACKAIMIANGXHIAIARBA0YEQCADQQFBASAAKAIgED5BAUZccgMMAQsgBEEBS1xyACACQRhqIgNBASACKAIQIANrIgMgACgCIBA+IANHXHIAIAIoAgwhAyAEQQFGXHIBDAILC0F/IQELIAJBIGokACABC2UBAX8CQCAALQAsRQRAIAJBACACQQBKGyECA0AgAiADRlxyAiAAIAEtAAAgACgCACgCNBECAEF/RgRAIAMPBSABQQFqIQEgA0EBaiEDDAELAAsACyABQQEgAiAAKAIgED4hAgsgAgsxACAAIAAoAgAoAhgRAAAaIAAgAUHCrMKZARBcciIBNgIkIAAgASABKAIAKAIcEQAAOgAsC8KnAgEEfyMAQSBrIgIkAEF/IQMCQCABQX9GBEAgAC0ANFxyASAAIAAoAjAiA0F/RzoANAwBCyAALQA0IQMCQAJAIAAtADVBAUdccgAgA0EBcUVccgBBfyEDIAAoAjAgACgCIBBEQX9GXHICDAELIANBAXFFXHIAIAIgACgCMDoAE0F/IQMCQAJAIAAoAiQiBCAAKAIoIAJBE2ogAkEUaiIFIAJBDGogAkEYaiACQSBqIAUgBCgCACgCDBEJAEEBaw4DAwMAAQsgACgCMCEEIAIgAkEZajYCFCACIAQ6ABgLA0AgAigCFCIEIAJBGGpNXHIBIAIgBEEBayIENgIUIAQsAAAgACgCIBBEQX9HXHIACwwBCyAAQQE6ADQgACABNgIwIAEhAwsgAkEgaiQAIAMLCQAgAEEBEMKJAgsJACAAQQAQwokCC0gAIAAgAUHCrMKZARBcciIBNgIkIAAgASABKAIAKAIYEQAANgIsIAAgACgCJCIBIAEoAgAoAhwRAAA6ADUgACgCLEEJTgRAECEACwscAEHCmMKNARA9QcK4wo8BED1Bw6TCkQEQwqMBQcKEwpQBEMKjAQsEAEIACwgAIAAQPBBcbgvClAEBBH8DQAJAIAIgA0xccgAgACgCGCIGIAAoAhwiBE8EQCAAIAEoAgAgACgCACgCNBECAEF/RlxyASADQQFqIQMgAUEEaiEBDAILIAIgA2siBSAEIAZrQQJ1IgQgBCAFShsiBUECdCIEBEAgBiABIATDvFxuAAALIAAgACgCGCAEajYCGCADIAVqIQMgASAEaiEBDAELCyADCzMBAn9BfyEBIAAgACgCACgCJBEAAEF/RwRAIAAoAgwiAigCACEBIAAgAkEEajYCDAsgAQvClgEBBH8DQAJAIAIgBExccgACfyAAKAIMIgYgACgCECIDSQRAIAIgBGsiBSADIAZrQQJ1IgMgAyAFShsiBUECdCIDBEAgASAGIAPDvFxuAAALIAAgACgCDCADajYCDCABIANqDAELIAAgACgCACgCKBEAACIDQX9GXHIBIAEgAzYCAEEBIQUgAUEEagshASAEIAVqIQQMAQsLIAQLDAAgABDCpAEaIAAQXG4LwowBAQR/A0ACQCACIARMXHIAIAAoAhgiBSAAKAIcIgNPBEAgACABLQAAIAAoAgAoAjQRAgBBf0ZccgEgBEEBaiEEIAFBAWohAQwCCyACIARrIgYgAyAFayIDIAMgBkobIgMEQCAFIAEgA8O8XG4AAAsgACAAKAIYIANqNgIYIAMgBGohBCABIANqIQEMAQsLIAQLMwECf0F/IQEgACAAKAIAKAIkEQAAQX9HBEAgACgCDCICLQAAIQEgACACQQFqNgIMCyABC8KJAQEEfwNAAkAgAiAETFxyAAJAIAAoAgwiBSAAKAIQIgNJBEAgAiAEayIGIAMgBWsiAyADIAZKGyIDBEAgASAFIAPDvFxuAAALIAAgACgCDCADajYCDAwBCyAAIAAoAgAoAigRAAAiA0F/RlxyASABIAM6AABBASEDCyABIANqIQEgAyAEaiEEDAELCyAECwwAIAAQwqgBGiAAEFxuC8KSBgEGf0HDnsKUAS0AAEUEQEHDtB0oAgAiBCEBQcO8wosBQgA3AgAjAEEQayICJABBw4TCiwEQwqACIgBBADoANCAAQX82AjAgAEHDvMKLATYCKCAAIAE2AiAgAEHDhCA2AgAgAkEMaiIDIAAoAgQiATYCACABQcOswpcBRwRAIAEgASgCBEEBajYCBAsgACADIAAoAgAoAggRAwAgAxAbIAJBEGokAEHCjMKMAUHCgBg2AgBBwoTCjAFBw6wXNgIAQcKowowBQQA2AgBBwojCjAFBADYCAEHCjMKMASAAEHZBw7gdKAIAIgVBwpjCjQFBw6DCjAEQwp8BQcO8HSgCACIBQcKowo4BQcOwwo0BEMKfASABQcK4wo8BQcKAwo8BEMKfAUHChMKMASgCAEEMaygCAEHDjMKMAWpBwpjCjQE2AgBBwqjCjgEoAgBBDGsiACgCAEHCrMKOAWoiAiACKAIAQcKAw4AAcjYCACAAKAIAQcOwwo4BakHCmMKNATYCAEHDiMKQAUIANwIAIwBBEGsiAyQAQcKQwpABEMKSAiIAQQA6ADQgAEF/NgIwIABBw4jCkAE2AiggACAENgIgIABBwpAiNgIAIANBDGoiBCAAKAIEIgI2AgAgAkHDrMKXAUcEQCACIAIoAgRBAWo2AgQLIAAgBCAAKAIAKAIIEQMAIAQQGyADQRBqJABBw5jCkAFBwpAZNgIAQcOQwpABQcO8GDYCAEHDtMKQAUEANgIAQcOUwpABQQA2AgBBw5jCkAEgABB2IAVBw6TCkQFBwqzCkQEQwp4BIAFBw7TCkgFBwrzCkgEQwp4BIAFBwoTClAFBw4zCkwEQwp4BQcOQwpABKAIAQQxrKAIAQcKYwpEBakHDpMKRATYCAEHDtMKSASgCAEEMayIAKAIAQcO4wpIBaiIBIAEoAgBBwoDDgAByNgIAIAAoAgBBwrzCkwFqQcOkwpEBNgIAQcOewpQBQQE6AAALIwBBEGsiACQAAkAgAEEMaiAAQQhqEAJccgBBwrTClQEgACgCDEECdEEEahAoIgE2AgAgAUVccgAgACgCCBAoIgEEQEHCtMKVASgCACICIAAoAgxBAnRqQQA2AgAgAiABEAhFXHIBC0HCtMKVAUEANgIACyAAQRBqJABBw4zDugBBw4DCpQU2AgBBwrTDugBBKjYCAEHDkMO6AEHCgMKABDYCAEHDlMO6AEHDqMOxACgCADYCAAsLwollLQBBwoAIC8KGCV19AHsib2siOjAsImVycm9yIjoiYmFkIGZlbiJ9AHsib2siOjAsImVycm9yIjoibm8gbW92ZSJ9ADAxMjM0NTY3ODlhYmNkZWZnaGlqa2xtbm9wcXJzdHV2d3h5egBpbmZpbml0eQBGZWJydWFyeQBKYW51YXJ5AEp1bHkAVGh1cnNkYXkAVHVlc2RheQBXZWRuZXNkYXkAU2F0dXJkYXkAU3VuZGF5AE1vbmRheQBGcmlkYXkATWF5ACVtLyVkLyV5AC0rICAgMFgweAAtMFgrMFggMFgtMHgrMHggMHgAVGhyZWFkU3RhdGUgbW92ZSBidWZmZXIgb3ZlcmZsb3cATW92ZSBidWZmZXIgb3ZlcmZsb3cATm92AFRodQB1bnN1cHBvcnRlZCBsb2NhbGUgZm9yIHN0YW5kYXJkIGlucHV0AEF1Z3VzdABPY3QAU2F0ACVzOiVkOiAlcwBBcHIAdmVjdG9yAG1vbmV5X2dldCBlcnJvcgBPY3RvYmVyAE5vdmVtYmVyAFNlcHRlbWJlcgBEZWNlbWJlcgBNYXIAL2Vtc2RrL2Vtc2NyaXB0ZW4vc3lzdGVtL2xpYi9saWJjeHhhYmkvc3JjL3ByaXZhdGVfdHlwZWluZm8uY3BwAFNlcAAlSTolTTolUyAlcABTdW4ASnVuADogbm8gY29udmVyc2lvbgBNb24AbmFuAEphbgBKdWwAQXByaWwARnJpAHN0b2kAYmFkX2FycmF5X25ld19sZW5ndGgATWFyY2gAQXVnAGJhc2ljX3N0cmluZwBpbmYAMDEyMzQ1Njc4OWFiY2RlZgAlLjBMZgAlTGYAbW92ZQBwaWVjZSBtaXNzaW5nIGluIFVuZG9Nb3ZlAHRydWUAVHVlAGZhbHNlAEp1bmUAOiBvdXQgb2YgcmFuZ2UAJTAqbGxkACUqbGxkACslbGxkACUrLjRsZABsb2NhbGUgbm90IHN1cHBvcnRlZABjbG9ja19nZXR0aW1lKENMT0NLX1JFQUxU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ZDdlN2Y4MDgxODI4Mzg0ODU4Njg3ODg4OThhOGI4YzhkOGU4ZjkwOTE5MjkzOTQ5NTk2OTc5ODk5OWE5YjljOWQ5ZTlmYTBhMWEyYTNhNGE1YTZhN2E4YTlhYWFiYWNhZGFlYWZiMGIxYjJiM2I0YjViNmI3YjhiOWJhYmJiY2JkYmViZmMwYzFjMmMzYzRjNWM2YzdjOGM5Y2FjYmNjY2RjZWNmZDBkMWQyZDNkNGQ1ZDZkN2Q4ZDlkYWRiZGNkZGRlZGZlMGUxZTJlM2U0ZTVlNmU3ZThlOWVhZWJlY2VkZWVlZmYwZjFmMmYzZjRmNWY2ZjdmOGY5ZmFmYmZjZmRmZWZmAAAAAAAAAABcbgAAAAAAAABkAAAAAAAAAMOoAwAAAAAAABBcJwAAAAAAAMKgwoYBAAAAAABAQg8AAAAAAMKAwpbCmAAAAAAAAMOhw7UFAAAAAADDisKaOwAAAAAAw6QLVAIAAAAAw6h2SBcAAAAAEMKlw5TDqAAAAADCoHJOGAkAAABAehDDs1oAAADCgMOGwqR+wo0DAAAAw4Fvw7LChiMAAADCil14RWMBAABkwqfCs8K2w6BccgAAw6jCiQQjw4fCisOkNgAAKDYAAE5TdDNfXzIxNF9fc2hhcmVkX2NvdW50RQAAAABoNwAAXFw2AAAAAAAAAQAAACA2AAAAAAAATlN0M19fMjE5X19zaGFyZWRfd2Vha19jb3VudEUAAAAMNwAAwog2AADDhDgAAE4xMF9fY3h4YWJpdjExNl9fc2hpbV90eXBlX2luZm9FAAAAAAw3AADCuDYAAHw2AABOMTBfX2N4eGFiaXYxMTdfX2NsYXNzX3R5cGVfaW5mb0UAAAAAAAAAwqw2AABdAQAAXgEAAF8BAABgAQAAYQEAAGIBAABjAQAAZAEAAAAAAAAsNwAAXQEAAGUBAABfAQAAYAEAAGEBAABmAQAAZwEAAGgBAAAMNwAAODcAAMKsNgAATjEwX19jeHhhYml2MTIwX19zaV9jbGFzc190eXBlX2luZm9FAAAAAAAAAADCiDcAAF0BAABpAQAAXwEAAGABAABhAQAAagEAAGsBAABsAQAADDcAAMKUNwAAwqw2AABOMTBfX2N4eGFiaXYxMjFfX3ZtaV9jbGFzc190eXBlX2luZm9FAAAAAAAAAAQ4AAABAAAAbQEAAG4BAADDpDYAAMOYNwAAU3Q5ZXhjZXB0aW9uAAAAAAw3AADDtDcAAMOQNwAAU3Q5YmFkX2FsbG9jAAAAAAw3AAAQOAAAw6g3AABTdDIwYmFkX2FycmF5X25ld19sZW5ndGgAAAAAAAAAAEA4AAACAAAAbwEAAHABAAAMNwAATDgAAMOQNwAAU3QxMWxvZ2ljX2Vycm9yAAAAAABwOAAAAgAAAHEBAABwAQAADDcAAHw4AABAOAAAU3QxMmxlbmd0aF9lcnJvcgAAAAAAAAAAwqQ4AAACAAAAcgEAAHABAAAMNwAAwrA4AABAOAAAU3QxMm91dF9vZl9yYW5nZQAAAADDpDYAAMOMOAAAU3Q5dHlwZV9pbmZvAEHDoMOxAAsRGMOEAADDgFIBAAAgAAAAAAAACQBBw7zDsQALATwAQcKQw7IACxI9AAAAAAAAAD4AAADCqD0AAAAEAEHCvMOyAAsEw7/Dv8O/w78AQcKAw7MACwEFAEHCjMOzAAsBPwBBwqTDswALDkAAAABBAAAAwrhBAAAABABBwrzDswALAQEAQcOMw7MACwXDv8O/w7/Dv1xuAEHCkMO0AAsJwoA5AAAAAAAABQBBwqTDtAALATwAQcK8w7QAC1xuQAAAAD4AAADDgEUAQcOUw7QACwECAEHDpMO0AAsIw7/Dv8O/w7/Dv8O/w7/DvwBBwqjDtQALIBg6AAAEPQAAJW0vJWQvJXkAAAAIJUg6JU06JVMAAAAIJyl9ZnVuY3Rpb24gZ2V0QmluYXJ5U3luYyhmaWxlKXtyZXR1cm4gZmlsZX1hc3luYyBmdW5jdGlvbiBnZXRXYXNtQmluYXJ5KGJpbmFyeUZpbGUpe3JldHVybiBnZXRCaW5hcnlTeW5jKGJpbmFyeUZpbGUpfWFzeW5jIGZ1bmN0aW9uIGluc3RhbnRpYXRlQXJyYXlCdWZmZXIoYmluYXJ5RmlsZSxpbXBvcnRzKXt0cnl7dmFyIGJpbmFyeT1hd2FpdCBnZXRXYXNtQmluYXJ5KGJpbmFyeUZpbGUpO3ZhciBpbnN0YW5jZT1hd2FpdCBXZWJBc3NlbWJseS5pbnN0YW50aWF0ZShiaW5hcnksaW1wb3J0cyk7cmV0dXJuIGluc3RhbmNlfWNhdGNoKHJlYXNvbil7ZXJyKGBmYWlsZWQgdG8gYXN5bmNocm9ub3VzbHkgcHJlcGFyZSB3YXNtOiAke3JlYXNvbn1gKTthYm9ydChyZWFzb24pfX1hc3luYyBmdW5jdGlvbiBpbnN0YW50aWF0ZUFzeW5jKGJpbmFyeSxiaW5hcnlGaWxlLGltcG9ydHMpe3JldHVybiBpbnN0YW50aWF0ZUFycmF5QnVmZmVyKGJpbmFyeUZpbGUsaW1wb3J0cyl9ZnVuY3Rpb24gZ2V0V2FzbUltcG9ydHMoKXt2YXIgaW1wb3J0cz17YTp3YXNtSW1wb3J0c307cmV0dXJuIGltcG9ydHN9YXN5bmMgZnVuY3Rpb24gY3JlYXRlV2FzbSgpe2Z1bmN0aW9uIHJlY2VpdmVJbnN0YW5jZShpbnN0YW5jZSl7d2FzbUV4cG9ydHM9aW5zdGFuY2UuZXhwb3J0czthc3NpZ25XYXNtRXhwb3J0cyh3YXNtRXhwb3J0cyk7dXBkYXRlTWVtb3J5Vmlld3MoKTtyZXR1cm4gd2FzbUV4cG9ydHN9ZnVuY3Rpb24gcmVjZWl2ZUluc3RhbnRpYXRpb25SZXN1bHQocmVzdWx0KXtyZXR1cm4gcmVjZWl2ZUluc3RhbmNlKHJlc3VsdFsiaW5zdGFuY2UiXSl9dmFyIGluZm89Z2V0V2FzbUltcG9ydHMoKTt2YXIgaW5zdGFudGlhdGVXYXNtPU1vZHVsZVsiaW5zdGFudGlhdGVXYXNtIl07aWYoaW5zdGFudGlhdGVXYXNtKXtyZXR1cm4gbmV3IFByb21pc2UocmVzb2x2ZT0+e2luc3RhbnRpYXRlV2FzbShpbmZvLGluc3Q9PnJlc29sdmUocmVjZWl2ZUluc3RhbmNlKGluc3QpKSl9KX13YXNtQmluYXJ5RmlsZT8/PWZpbmRXYXNtQmluYXJ5KCk7dmFyIHJlc3VsdD1hd2FpdCBpbnN0YW50aWF0ZUFzeW5jKHdhc21CaW5hcnksd2FzbUJpbmFyeUZpbGUsaW5mbyk7dmFyIGV4cG9ydHM9cmVjZWl2ZUluc3RhbnRpYXRpb25SZXN1bHQocmVzdWx0KTtyZXR1cm4gZXhwb3J0c31jbGFzcyBFeGl0U3RhdHVze25hbWU9IkV4aXRTdGF0dXMiO2NvbnN0cnVjdG9yKHN0YXR1cyl7dGhpcy5tZXNzYWdlPWBQcm9ncmFtIHRlcm1pbmF0ZWQgd2l0aCBleGl0KCR7c3RhdHVzfSlgO3RoaXMuc3RhdHVzPXN0YXR1c319dmFyIEhFQVA4O3ZhciBjYWxsUnVudGltZUNhbGxiYWNrcz1jYWxsYmFja3M9Pnt3aGlsZShjYWxsYmFja3MubGVuZ3RoPjApe2NhbGxiYWNrcy5zaGlmdCgpKE1vZHVsZSl9fTt2YXIgb25Qb3N0UnVucz1bXTt2YXIgb25QcmVSdW5zPVtdO3ZhciBub0V4aXRSdW50aW1lPXRydWU7dmFyIHN0YWNrUmVzdG9yZT12YWw9Pl9fZW1zY3JpcHRlbl9zdGFja19yZXN0b3JlKHZhbCk7dmFyIHN0YWNrU2F2ZT0oKT0+X2Vtc2NyaXB0ZW5fc3RhY2tfZ2V0X2N1cnJlbnQoKTt2YXIgSEVBUFUzMjtjbGFzcyBFeGNlcHRpb25JbmZve2NvbnN0cnVjdG9yKGV4Y1B0cil7dGhpcy5leGNQdHI9ZXhjUHRyO3RoaXMucHRyPWV4Y1B0ci0yNH1zZXRfdHlwZSh0eXBlKXtIRUFQVTMyW3RoaXMucHRyKzQ+PjJdPXR5cGV9Z2V0X3R5cGUoKXtyZXR1cm4gSEVBUFUzMlt0aGlzLnB0cis0Pj4yXX1zZXRfZGVzdHJ1Y3RvcihkZXN0cnVjdG9yKXtIRUFQVTMyW3RoaXMucHRyKzg+PjJdPWRlc3RydWN0b3J9Z2V0X2Rlc3RydWN0b3IoKXtyZXR1cm4gSEVBUFUzMlt0aGlzLnB0cis4Pj4yXX1zZXRfY2F1Z2h0KGNhdWdodCl7Y2F1Z2h0PWNhdWdodD8xOjA7SEVBUDhbdGhpcy5wdHIrMTJdPWNhdWdodH1nZXRfY2F1Z2h0KCl7cmV0dXJuIEhFQVA4W3RoaXMucHRyKzEyXSE9MH1zZXRfcmV0aHJvd24ocmV0aHJvd24pe3JldGhyb3duPXJldGhyb3duPzE6MDtIRUFQOFt0aGlzLnB0cisxM109cmV0aHJvd259Z2V0X3JldGhyb3duKCl7cmV0dXJuIEhFQVA4W3RoaXMucHRyKzEzXSE9MH1pbml0KHR5cGUsZGVzdHJ1Y3Rvcil7dGhpcy5zZXRfYWRqdXN0ZWRfcHRyKDApO3RoaXMuc2V0X3R5cGUodHlwZSk7dGhpcy5zZXRfZGVzdHJ1Y3RvcihkZXN0cnVjdG9yKX1zZXRfYWRqdXN0ZWRfcHRyKGFkanVzdGVkUHRyKXtIRUFQVTMyW3RoaXMucHRyKzE2Pj4yXT1hZGp1c3RlZFB0cn1nZXRfYWRqdXN0ZWRfcHRyKCl7cmV0dXJuIEhFQVBVMzJbdGhpcy5wdHIrMTY+PjJdfX12YXIgdW5jYXVnaHRFeGNlcHRpb25Db3VudD0wO3ZhciBfX1Vud2luZF9SYWlzZUV4Y2VwdGlvbj1leD0+e2Fib3J0KCl9O3ZhciBfX19jeGFfdGhyb3c9KHB0cix0eXBlLGRlc3RydWN0b3IpPT57dmFyIGluZm89bmV3IEV4Y2VwdGlvbkluZm8ocHRyKTtpbmZvLmluaXQodHlwZSxkZXN0cnVjdG9yKTt1bmNhdWdodEV4Y2VwdGlvbkNvdW50Kys7X19VbndpbmRfUmFpc2VFeGNlcHRpb24ocHRyKX07dmFyIF9fYWJvcnRfanM9KCk9PmFib3J0KCIiKTt2YXIgc3RyaW5nVG9VVEY4QXJyYXk9KHN0cixoZWFwLG91dElkeCxtYXhCeXRlc1RvV3JpdGUpPT57aWYoIShtYXhCeXRlc1RvV3JpdGU+MCkpcmV0dXJuIDA7dmFyIHN0YXJ0SWR4PW91dElkeDt2YXIgZW5kSWR4PW91dElkeCttYXhCeXRlc1RvV3JpdGUtMTtmb3IodmFyIGk9MDtpPHN0ci5sZW5ndGg7KytpKXt2YXIgdT1zdHIuY29kZVBvaW50QXQoaSk7aWYodTw9MTI3KXtpZihvdXRJZHg+PWVuZElkeClicmVhaztoZWFwW291dElkeCsrXT11fWVsc2UgaWYodTw9MjA0Nyl7aWYob3V0SWR4KzE+PWVuZElkeClicmVhaztoZWFwW291dElkeCsrXT0xOTJ8dT4+NjtoZWFwW291dElkeCsrXT0xMjh8dSY2M31lbHNlIGlmKHU8PTY1NTM1KXtpZihvdXRJZHgrMj49ZW5kSWR4KWJyZWFrO2hlYXBbb3V0SWR4KytdPTIyNHx1Pj4xMjtoZWFwW291dElkeCsrXT0xMjh8dT4+NiY2MztoZWFwW291dElkeCsrXT0xMjh8dSY2M31lbHNle2lmKG91dElkeCszPj1lbmRJZHgpYnJlYWs7aGVhcFtvdXRJZHgrK109MjQwfHU+PjE4O2hlYXBbb3V0SWR4KytdPTEyOHx1Pj4xMiY2MztoZWFwW291dElkeCsrXT0xMjh8dT4+NiY2MztoZWFwW291dElkeCsrXT0xMjh8dSY2MztpKyt9fWhlYXBbb3V0SWR4XT0wO3JldHVybiBvdXRJZHgtc3RhcnRJZHh9O3ZhciBIRUFQVTg7dmFyIHN0cmluZ1RvVVRGOD0oc3RyLG91dFB0cixtYXhCeXRlc1RvV3JpdGUpPT5zdHJpbmdUb1VURjhBcnJheShzdHIsSEVBUFU4LG91dFB0cixtYXhCeXRlc1RvV3JpdGUpO3ZhciBIRUFQMzI7dmFyIF9lbXNjcmlwdGVuX2dldF9ub3c9KCk9PnBlcmZvcm1hbmNlLm5vdygpO3ZhciBfZW1zY3JpcHRlbl9kYXRlX25vdz0oKT0+RGF0ZS5ub3coKTt2YXIgbm93SXNNb25vdG9uaWM9MTt2YXIgY2hlY2tXYXNpQ2xvY2s9Y2xvY2tfaWQ9PmNsb2NrX2lkPj0wJiZjbG9ja19pZDw9Mzt2YXIgSU5UNTNfTUFYPTkwMDcxOTkyNTQ3NDA5OTI7dmFyIElOVDUzX01JTj0tOTAwNzE5OTI1NDc0MDk5Mjt2YXIgYmlnaW50VG9JNTNDaGVja2VkPW51bT0+bnVtPElOVDUzX01JTnx8bnVtPklOVDUzX01BWD9OYU46TnVtYmVyKG51bSk7dmFyIEhFQVA2NDtmdW5jdGlvbiBfY2xvY2tfdGltZV9nZXQoY2xrX2lkLGlnbm9yZWRfcHJlY2lzaW9uLHB0aW1lKXtpZ25vcmVkX3ByZWNpc2lvbj1iaWdpbnRUb0k1M0NoZWNrZWQoaWdub3JlZF9wcmVjaXNpb24pO2lmKCFjaGVja1dhc2lDbG9jayhjbGtfaWQpKXtyZXR1cm4gMjh9dmFyIG5vdztpZihjbGtfaWQ9PT0wKXtub3c9X2Vtc2NyaXB0ZW5fZGF0ZV9ub3coKX1lbHNlIGlmKG5vd0lzTW9ub3RvbmljKXtub3c9X2Vtc2NyaXB0ZW5fZ2V0X25vdygpfWVsc2V7cmV0dXJuIDUyfXZhciBuc2VjPU1hdGgucm91bmQobm93KjFlMyoxZTMpO0hFQVA2NFtwdGltZT4+M109QmlnSW50KG5zZWMpO3JldHVybiAwfXZhciBnZXRIZWFwTWF4PSgpPT4yMTQ3NDgzNjQ4O3ZhciBhbGlnbk1lbW9yeT0oc2l6ZSxhbGlnbm1lbnQpPT5NYXRoLmNlaWwoc2l6ZS9hbGlnbm1lbnQpKmFsaWdubWVudDt2YXIgZ3Jvd01lbW9yeT1zaXplPT57dmFyIG9sZEhlYXBTaXplPXdhc21NZW1vcnkuYnVmZmVyLmJ5dGVMZW5ndGg7dmFyIHBhZ2VzPShzaXplLW9sZEhlYXBTaXplKzY1NTM1KS82NTUzNnwwO3RyeXt3YXNtTWVtb3J5Lmdyb3cocGFnZXMpO3VwZGF0ZU1lbW9yeVZpZXdzKCk7cmV0dXJuIDF9Y2F0Y2goZSl7fX07dmFyIF9lbXNjcmlwdGVuX3Jlc2l6ZV9oZWFwPXJlcXVlc3RlZFNpemU9Pnt2YXIgb2xkU2l6ZT1IRUFQVTgubGVuZ3RoO3JlcXVlc3RlZFNpemU+Pj49MDt2YXIgbWF4SGVhcFNpemU9Z2V0SGVhcE1heCgpO2lmKHJlcXVlc3RlZFNpemU+bWF4SGVhcFNpemUpe3JldHVybiBmYWxzZX1mb3IodmFyIGN1dERvd249MTtjdXREb3duPD00O2N1dERvd24qPTIpe3ZhciBvdmVyR3Jvd25IZWFwU2l6ZT1vbGRTaXplKigxKy4yL2N1dERvd24pO292ZXJHcm93bkhlYXBTaXplPU1hdGgubWluKG92ZXJHcm93bkhlYXBTaXplLHJlcXVlc3RlZFNpemUrMTAwNjYzMjk2KTt2YXIgbmV3U2l6ZT1NYXRoLm1pbihtYXhIZWFwU2l6ZSxhbGlnbk1lbW9yeShNYXRoLm1heChyZXF1ZXN0ZWRTaXplLG92ZXJHcm93bkhlYXBTaXplKSw2NTUzNikpO3ZhciByZXBsYWNlbWVudD1ncm93TWVtb3J5KG5ld1NpemUpO2lmKHJlcGxhY2VtZW50KXtyZXR1cm4gdHJ1ZX19cmV0dXJuIGZhbHNlfTt2YXIgRU5WPXt9O3ZhciBnZXRFeGVjdXRhYmxlTmFtZT0oKT0+dGhpc1Byb2dyYW07dmFyIGdldEVudlN0cmluZ3M9KCk9PntpZighZ2V0RW52U3RyaW5ncy5zdHJpbmdzKXt2YXIgbGFuZz0oZ2xvYmFsVGhpcy5uYXZpZ2F0b3I/Lmxhbmd1YWdlPz8iQyIpLnJlcGxhY2UoIi0iLCJfIikrIi5VVEYtOCI7dmFyIGVudj17VVNFUjoid2ViX3VzZXIiLExPR05BTUU6IndlYl91c2VyIixQQVRIOiIvIixQV0Q6Ii8iLEhPTUU6Ii9ob21lL3dlYl91c2VyIixMQU5HOmxhbmcsXzpnZXRFeGVjdXRhYmxlTmFtZSgpfTtmb3IodmFyIHggaW4gRU5WKXtpZihFTlZbeF09PT11bmRlZmluZWQpZGVsZXRlIGVudlt4XTtlbHNlIGVudlt4XT1FTlZbeF19dmFyIHN0cmluZ3M9W107Zm9yKHZhciB4IGluIGVudil7c3RyaW5ncy5wdXNoKGAke3h9PSR7ZW52W3hdfWApfWdldEVudlN0cmluZ3Muc3RyaW5ncz1zdHJpbmdzfXJldHVybiBnZXRFbnZTdHJpbmdzLnN0cmluZ3N9O3ZhciBfZW52aXJvbl9nZXQ9KF9fZW52aXJvbixlbnZpcm9uX2J1Zik9Pnt2YXIgYnVmU2l6ZT0wO3ZhciBlbnZwPTA7Zm9yKHZhciBzdHJpbmcgb2YgZ2V0RW52U3RyaW5ncygpKXt2YXIgcHRyPWVudmlyb25fYnVmK2J1ZlNpemU7SEVBUFUzMltfX2Vudmlyb24rZW52cD4+Ml09cHRyO2J1ZlNpemUrPXN0cmluZ1RvVVRGOChzdHJpbmcscHRyLEluZmluaXR5KSsxO2VudnArPTR9cmV0dXJuIDB9O3ZhciBsZW5ndGhCeXRlc1VURjg9c3RyPT57dmFyIGxlbj0wO2Zvcih2YXIgaT0wO2k8c3RyLmxlbmd0aDsrK2kpe3ZhciBjPXN0ci5jaGFyQ29kZUF0KGkpO2lmKGM8PTEyNyl7bGVuKyt9ZWxzZSBpZihjPD0yMDQ3KXtsZW4rPTJ9ZWxzZSBpZihjPj01NTI5NiYmYzw9NTczNDMpe2xlbis9NDsrK2l9ZWxzZXtsZW4rPTN9fXJldHVybiBsZW59O3ZhciBfZW52aXJvbl9zaXplc19nZXQ9KHBlbnZpcm9uX2NvdW50LHBlbnZpcm9uX2J1Zl9zaXplKT0+e3ZhciBzdHJpbmdzPWdldEVudlN0cmluZ3MoKTtIRUFQVTMyW3BlbnZpcm9uX2NvdW50Pj4yXT1zdHJpbmdzLmxlbmd0aDt2YXIgYnVmU2l6ZT0wO2Zvcih2YXIgc3RyaW5nIG9mIHN0cmluZ3Mpe2J1ZlNpemUrPWxlbmd0aEJ5dGVzVVRGOChzdHJpbmcpKzF9SEVBUFUzMltwZW52aXJvbl9idWZfc2l6ZT4+Ml09YnVmU2l6ZTtyZXR1cm4gMH07dmFyIFBBVEg9e2lzQWJzOnBhdGg9PnBhdGguY2hhckF0KDApPT09Ii8iLHNwbGl0UGF0aDpmaWxlbmFtZT0+e3ZhciBzcGxpdFBhdGhSZT0vXihcLz98KShbXHNcU10qPykoKD86XC57MSwyfXxbXlwvXSs/fCkoXC5bXi5cL10qfCkpKD86W1wvXSopJC87cmV0dXJuIHNwbGl0UGF0aFJlLmV4ZWMoZmlsZW5hbWUpLnNsaWNlKDEpfSxub3JtYWxpemVBcnJheToocGFydHMsYWxsb3dBYm92ZVJvb3QpPT57dmFyIHVwPTA7Zm9yKHZhciBpPXBhcnRzLmxlbmd0aC0xO2k+PTA7aS0tKXt2YXIgbGFzdD1wYXJ0c1tpXTtpZihsYXN0PT09Ii4iKXtwYXJ0cy5zcGxpY2UoaSwxKX1lbHNlIGlmKGxhc3Q9PT0iLi4iKXtwYXJ0cy5zcGxpY2UoaSwxKTt1cCsrfWVsc2UgaWYodXApe3BhcnRzLnNwbGljZShpLDEpO3VwLS19fWlmKGFsbG93QWJvdmVSb290KXtmb3IoO3VwO3VwLS0pe3BhcnRzLnVuc2hpZnQoIi4uIil9fXJldHVybiBwYXJ0c30sbm9ybWFsaXplOnBhdGg9Pnt2YXIgaXNBYnNvbHV0ZT1QQVRILmlzQWJzKHBhdGgpLHRyYWlsaW5nU2xhc2g9cGF0aC5zbGljZSgtMSk9PT0iLyI7cGF0aD1QQVRILm5vcm1hbGl6ZUFycmF5KHBhdGguc3BsaXQoIi8iKS5maWx0ZXIocD0+ISFwKSwhaXNBYnNvbHV0ZSkuam9pbigiLyIpO2lmKCFwYXRoJiYhaXNBYnNvbHV0ZSl7cGF0aD0iLiJ9aWYocGF0aCYmdHJhaWxpbmdTbGFzaCl7cGF0aCs9Ii8ifXJldHVybihpc0Fic29sdXRlPyIvIjoiIikrcGF0aH0sZGlybmFtZTpwYXRoPT57dmFyIHJlc3VsdD1QQVRILnNwbGl0UGF0aChwYXRoKSxyb290PXJlc3VsdFswXSxkaXI9cmVzdWx0WzFdO2lmKCFyb290JiYhZGlyKXtyZXR1cm4iLiJ9aWYoZGlyKXtkaXI9ZGlyLnNsaWNlKDAsLTEpfXJldHVybiByb290K2Rpcn0sYmFzZW5hbWU6cGF0aD0+cGF0aCYmcGF0aC5tYXRjaCgvKFteXC9dK3xcLylcLyokLylbMV0sam9pbjooLi4ucGF0aHMpPT5QQVRILm5vcm1hbGl6ZShwYXRocy5qb2luKCIvIikpLGpvaW4yOihsLHIpPT5QQVRILm5vcm1hbGl6ZShsKyIvIityKX07dmFyIGluaXRSYW5kb21GaWxsPSgpPT57aWYoRU5WSVJPTk1FTlRfSVNfTk9ERSl7dmFyIG5vZGVDcnlwdG89cmVxdWlyZSgibm9kZTpjcnlwdG8iKTtyZXR1cm4gdmlldz0+KG5vZGVDcnlwdG8ucmFuZG9tRmlsbFN5bmModmlldyksMCl9cmV0dXJuIHZpZXc9PihjcnlwdG8uZ2V0UmFuZG9tVmFsdWVzKHZpZXcpLDApfTt2YXIgcmFuZG9tRmlsbD12aWV3PT4ocmFuZG9tRmlsbD1pbml0UmFuZG9tRmlsbCgpKSh2aWV3KTt2YXIgUEFUSF9GUz17cmVzb2x2ZTooLi4uYXJncyk9Pnt2YXIgcmVzb2x2ZWRQYXRoPSIiLHJlc29sdmVkQWJzb2x1dGU9ZmFsc2U7Zm9yKHZhciBpPWFyZ3MubGVuZ3RoLTE7aT49LTEmJiFyZXNvbHZlZEFic29sdXRlO2ktLSl7dmFyIHBhdGg9aT49MD9hcmdzW2ldOkZTLmN3ZCgpO2lmKHR5cGVvZiBwYXRoIT0ic3RyaW5nIil7dGhyb3cgbmV3IFR5cGVFcnJvcigiQXJndW1lbnRzIHRvIHBhdGgucmVzb2x2ZSBtdXN0IGJlIHN0cmluZ3MiKX1lbHNlIGlmKCFwYXRoKXtyZXR1cm4iIn1yZXNvbHZlZFBhdGg9cGF0aCsiLyIrcmVzb2x2ZWRQYXRoO3Jlc29sdmVkQWJzb2x1dGU9UEFUSC5pc0FicyhwYXRoKX1yZXNvbHZlZFBhdGg9UEFUSC5ub3JtYWxpemVBcnJheShyZXNvbHZlZFBhdGguc3BsaXQoIi8iKS5maWx0ZXIocD0+ISFwKSwhcmVzb2x2ZWRBYnNvbHV0ZSkuam9pbigiLyIpO3JldHVybihyZXNvbHZlZEFic29sdXRlPyIvIjoiIikrcmVzb2x2ZWRQYXRofHwiLiJ9LHJlbGF0aXZlOihmcm9tLHRvKT0+e2Zyb209UEFUSF9GUy5yZXNvbHZlKGZyb20pLnNsaWNlKDEpO3RvPVBBVEhfRlMucmVzb2x2ZSh0bykuc2xpY2UoMSk7ZnVuY3Rpb24gdHJpbShhcnIpe3ZhciBzdGFydD0wO2Zvcig7c3RhcnQ8YXJyLmxlbmd0aDtzdGFydCsrKXtpZihhcnJbc3RhcnRdIT09IiIpYnJlYWt9dmFyIGVuZD1hcnIubGVuZ3RoLTE7Zm9yKDtlbmQ+PTA7ZW5kLS0pe2lmKGFycltlbmRdIT09IiIpYnJlYWt9aWYoc3RhcnQ+ZW5kKXJldHVybltdO3JldHVybiBhcnIuc2xpY2Uoc3RhcnQsZW5kLXN0YXJ0KzEpfXZhciBmcm9tUGFydHM9dHJpbShmcm9tLnNwbGl0KCIvIikpO3ZhciB0b1BhcnRzPXRyaW0odG8uc3BsaXQoIi8iKSk7dmFyIGxlbmd0aD1NYXRoLm1pbihmcm9tUGFydHMubGVuZ3RoLHRvUGFydHMubGVuZ3RoKTt2YXIgc2FtZVBhcnRzTGVuZ3RoPWxlbmd0aDtmb3IodmFyIGk9MDtpPGxlbmd0aDtpKyspe2lmKGZyb21QYXJ0c1tpXSE9PXRvUGFydHNbaV0pe3NhbWVQYXJ0c0xlbmd0aD1pO2JyZWFrfX12YXIgb3V0cHV0UGFydHM9W107Zm9yKHZhciBpPXNhbWVQYXJ0c0xlbmd0aDtpPGZyb21QYXJ0cy5sZW5ndGg7aSsrKXtvdXRwdXRQYXJ0cy5wdXNoKCIuLiIpfW91dHB1dFBhcnRzPW91dHB1dFBhcnRzLmNvbmNhdCh0b1BhcnRzLnNsaWNlKHNhbWVQYXJ0c0xlbmd0aCkpO3JldHVybiBvdXRwdXRQYXJ0cy5qb2luKCIvIil9fTt2YXIgVVRGOERlY29kZXI9Z2xvYmFsVGhpcy5UZXh0RGVjb2RlciYmbmV3IFRleHREZWNvZGVyO3ZhciBmaW5kU3RyaW5nRW5kPShoZWFwT3JBcnJheSxpZHgsbWF4Qnl0ZXNUb1JlYWQsaWdub3JlTnVsKT0+e3ZhciBtYXhJZHg9aWR4K21heEJ5dGVzVG9SZWFkO2lmKGlnbm9yZU51bClyZXR1cm4gbWF4SWR4O3doaWxlKGhlYXBPckFycmF5W2lkeF0mJiEoaWR4Pj1tYXhJZHgpKSsraWR4O3JldHVybiBpZHh9O3ZhciBVVEY4QXJyYXlUb1N0cmluZz0oaGVhcE9yQXJyYXksaWR4PTAsbWF4Qnl0ZXNUb1JlYWQsaWdub3JlTnVsKT0+e3ZhciBlbmRQdHI9ZmluZFN0cmluZ0VuZChoZWFwT3JBcnJheSxpZHgsbWF4Qnl0ZXNUb1JlYWQsaWdub3JlTnVsKTtpZihlbmRQdHItaWR4PjE2JiZoZWFwT3JBcnJheS5idWZmZXImJlVURjhEZWNvZGVyKXtyZXR1cm4gVVRGOERlY29kZXIuZGVjb2RlKGhlYXBPckFycmF5LnN1YmFycmF5KGlkeCxlbmRQdHIpKX12YXIgc3RyPSIiO3doaWxlKGlkeDxlbmRQdHIpe3ZhciB1MD1oZWFwT3JBcnJheVtpZHgrK107aWYoISh1MCYxMjgpKXtzdHIrPVN0cmluZy5mcm9tQ2hhckNvZGUodTApO2NvbnRpbnVlfXZhciB1MT1oZWFwT3JBcnJheVtpZHgrK10mNjM7aWYoKHUwJjIyNCk9PTE5Mil7c3RyKz1TdHJpbmcuZnJvbUNoYXJDb2RlKCh1MCYzMSk8PDZ8dTEpO2NvbnRpbnVlfXZhciB1Mj1oZWFwT3JBcnJheVtpZHgrK10mNjM7aWYoKHUwJjI0MCk9PTIyNCl7dTA9KHUwJjE1KTw8MTJ8dTE8PDZ8dTJ9ZWxzZXt1MD0odTAmNyk8PDE4fHUxPDwxMnx1Mjw8NnxoZWFwT3JBcnJheVtpZHgrK10mNjN9aWYodTA8NjU1MzYpe3N0cis9U3RyaW5nLmZyb21DaGFyQ29kZSh1MCl9ZWxzZXt2YXIgY2g9dTAtNjU1MzY7c3RyKz1TdHJpbmcuZnJvbUNoYXJDb2RlKDU1Mjk2fGNoPj4xMCw1NjMyMHxjaCYxMDIzKX19cmV0dXJuIHN0cn07dmFyIEZTX3N0ZGluX2dldENoYXJfYnVmZmVyPVtdO3ZhciBpbnRBcnJheUZyb21TdHJpbmc9KHN0cmluZ3ksZG9udEFkZE51bGwsbGVuZ3RoKT0+e3ZhciBsZW49bGVuZ3RoPjA/bGVuZ3RoOmxlbmd0aEJ5dGVzVVRGOChzdHJpbmd5KSsxO3ZhciB1OGFycmF5PW5ldyBBcnJheShsZW4pO3ZhciBudW1CeXRlc1dyaXR0ZW49c3RyaW5nVG9VVEY4QXJyYXkoc3RyaW5neSx1OGFycmF5LDAsdThhcnJheS5sZW5ndGgpO2lmKGRvbnRBZGROdWxsKXU4YXJyYXkubGVuZ3RoPW51bUJ5dGVzV3JpdHRlbjtyZXR1cm4gdThhcnJheX07dmFyIEZTX3N0ZGluX2dldENoYXI9KCk9PntpZighRlNfc3RkaW5fZ2V0Q2hhcl9idWZmZXIubGVuZ3RoKXt2YXIgcmVzdWx0PW51bGw7aWYoRU5WSVJPTk1FTlRfSVNfTk9ERSl7dmFyIEJVRlNJWkU9MjU2O3ZhciBidWY9QnVmZmVyLmFsbG9jKEJVRlNJWkUpO3ZhciBieXRlc1JlYWQ9MDt2YXIgZmQ9cHJvY2Vzcy5zdGRpbi5mZDt0cnl7Ynl0ZXNSZWFkPWZzLnJlYWRTeW5jKGZkLGJ1ZiwwLEJVRlNJWkUpfWNhdGNoKGUpe2lmKGUudG9TdHJpbmcoKS5pbmNsdWRlcygiRU9GIikpYnl0ZXNSZWFkPTA7ZWxzZSB0aHJvdyBlfWlmKGJ5dGVzUmVhZD4wKXtyZXN1bHQ9YnVmLnNsaWNlKDAsYnl0ZXNSZWFkKS50b1N0cmluZygidXRmLTgiKX19ZWxzZSBpZihnbG9iYWxUaGlzLndpbmRvdz8ucHJvbXB0KXtyZXN1bHQ9d2luZG93LnByb21wdCgiSW5wdXQ6ICIpO2lmKHJlc3VsdCE9PW51bGwpe3Jlc3VsdCs9IlxuIn19ZWxzZXt9aWYoIXJlc3VsdCl7cmV0dXJuIG51bGx9RlNfc3RkaW5fZ2V0Q2hhcl9idWZmZXI9aW50QXJyYXlGcm9tU3RyaW5nKHJlc3VsdCx0cnVlKX1yZXR1cm4gRlNfc3RkaW5fZ2V0Q2hhcl9idWZmZXIuc2hpZnQoKX07dmFyIFRUWT17dHR5czpbXSxpbml0KCl7fSxzaHV0ZG93bigpe30scmVnaXN0ZXIoZGV2LG9wcyl7VFRZLnR0eXNbZGV2XT17aW5wdXQ6W10sb3V0cHV0OltdLG9wc307RlMucmVnaXN0ZXJEZXZpY2UoZGV2LFRUWS5zdHJlYW1fb3BzKX0sc3RyZWFtX29wczp7b3BlbihzdHJlYW0pe3ZhciB0dHk9VFRZLnR0eXNbc3RyZWFtLm5vZGUucmRldl07aWYoIXR0eSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNDMpfXN0cmVhbS50dHk9dHR5O3N0cmVhbS5zZWVrYWJsZT1mYWxzZX0sY2xvc2Uoc3RyZWFtKXtzdHJlYW0udHR5Lm9wcy5mc3luYyhzdHJlYW0udHR5KX0sZnN5bmMoc3RyZWFtKXtzdHJlYW0udHR5Lm9wcy5mc3luYyhzdHJlYW0udHR5KX0scmVhZChzdHJlYW0sYnVmZmVyLG9mZnNldCxsZW5ndGgscG9zKXtpZighc3RyZWFtLnR0eXx8IXN0cmVhbS50dHkub3BzLmdldF9jaGFyKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig2MCl9dmFyIGJ5dGVzUmVhZD0wO2Zvcih2YXIgaT0wO2k8bGVuZ3RoO2krKyl7dmFyIHJlc3VsdDt0cnl7cmVzdWx0PXN0cmVhbS50dHkub3BzLmdldF9jaGFyKHN0cmVhbS50dHkpfWNhdGNoKGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI5KX1pZihyZXN1bHQ9PT11bmRlZmluZWQmJiFieXRlc1JlYWQpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDYpfWlmKHJlc3VsdD09PW51bGx8fHJlc3VsdD09PXVuZGVmaW5lZClicmVhaztieXRlc1JlYWQrKztidWZmZXJbb2Zmc2V0K2ldPXJlc3VsdDtpZihyZXN1bHQ9PT0xMClicmVha31pZihieXRlc1JlYWQpe3N0cmVhbS5ub2RlLmF0aW1lPURhdGUubm93KCl9cmV0dXJuIGJ5dGVzUmVhZH0sd3JpdGUoc3RyZWFtLGJ1ZmZlcixvZmZzZXQsbGVuZ3RoLHBvcyl7aWYoIXN0cmVhbS50dHl8fCFzdHJlYW0udHR5Lm9wcy5wdXRfY2hhcil7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNjApfXRyeXtmb3IodmFyIGk9MDtpPGxlbmd0aDtpKyspe3N0cmVhbS50dHkub3BzLnB1dF9jaGFyKHN0cmVhbS50dHksYnVmZmVyW29mZnNldCtpXSl9fWNhdGNoKGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI5KX1pZihsZW5ndGgpe3N0cmVhbS5ub2RlLm10aW1lPXN0cmVhbS5ub2RlLmN0aW1lPURhdGUubm93KCl9cmV0dXJuIGl9fSxkZWZhdWx0X3R0eV9vcHM6e2dldF9jaGFyKHR0eSl7cmV0dXJuIEZTX3N0ZGluX2dldENoYXIoKX0scHV0X2NoYXIodHR5LHZhbCl7aWYodmFsPT09bnVsbHx8dmFsPT09MTApe291dChVVEY4QXJyYXlUb1N0cmluZyh0dHkub3V0cHV0KSk7dHR5Lm91dHB1dD1bXX1lbHNle2lmKHZhbCE9MCl0dHkub3V0cHV0LnB1c2godmFsKX19LGZzeW5jKHR0eSl7aWYodHR5Lm91dHB1dD8ubGVuZ3RoPjApe291dChVVEY4QXJyYXlUb1N0cmluZyh0dHkub3V0cHV0KSk7dHR5Lm91dHB1dD1bXX19LGlvY3RsX3RjZ2V0cyh0dHkpe3JldHVybntjX2lmbGFnOjI1ODU2LGNfb2ZsYWc6NSxjX2NmbGFnOjE5MSxjX2xmbGFnOjM1Mzg3LGNfY2M6WzMsMjgsMTI3LDIxLDQsMCwxLDAsMTcsMTksMjYsMCwxOCwxNSwyMywyMiwwLDAsMCwwLDAsMCwwLDAsMCwwLDAsMCwwLDAsMCwwXX19LGlvY3RsX3Rjc2V0cyh0dHksb3B0aW9uYWxfYWN0aW9ucyxkYXRhKXtyZXR1cm4gMH0saW9jdGxfdGlvY2d3aW5zeih0dHkpe3JldHVyblsyNCw4MF19fSxkZWZhdWx0X3R0eTFfb3BzOntwdXRfY2hhcih0dHksdmFsKXtpZih2YWw9PT1udWxsfHx2YWw9PT0xMCl7ZXJyKFVURjhBcnJheVRvU3RyaW5nKHR0eS5vdXRwdXQpKTt0dHkub3V0cHV0PVtdfWVsc2V7aWYodmFsIT0wKXR0eS5vdXRwdXQucHVzaCh2YWwpfX0sZnN5bmModHR5KXtpZih0dHkub3V0cHV0Py5sZW5ndGg+MCl7ZXJyKFVURjhBcnJheVRvU3RyaW5nKHR0eS5vdXRwdXQpKTt0dHkub3V0cHV0PVtdfX19fTt2YXIgbW1hcEFsbG9jPXNpemU9PnthYm9ydCgpfTt2YXIgTUVNRlM9e29wc190YWJsZTpudWxsLG1vdW50KG1vdW50KXtyZXR1cm4gTUVNRlMuY3JlYXRlTm9kZShudWxsLCIvIiwxNjg5NSwwKX0sY3JlYXRlTm9kZShwYXJlbnQsbmFtZSxtb2RlLGRldil7aWYoRlMuaXNCbGtkZXYobW9kZSl8fEZTLmlzRklGTyhtb2RlKSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNjMpfU1FTUZTLm9wc190YWJsZXx8PXtkaXI6e25vZGU6e2dldGF0dHI6TUVNRlMubm9kZV9vcHMuZ2V0YXR0cixzZXRhdHRyOk1FTUZTLm5vZGVfb3BzLnNldGF0dHIsbG9va3VwOk1FTUZTLm5vZGVfb3BzLmxvb2t1cCxta25vZDpNRU1GUy5ub2RlX29wcy5ta25vZCxyZW5hbWU6TUVNRlMubm9kZV9vcHMucmVuYW1lLHVubGluazpNRU1GUy5ub2RlX29wcy51bmxpbmsscm1kaXI6TUVNRlMubm9kZV9vcHMucm1kaXIscmVhZGRpcjpNRU1GUy5ub2RlX29wcy5yZWFkZGlyLHN5bWxpbms6TUVNRlMubm9kZV9vcHMuc3ltbGlua30sc3RyZWFtOntsbHNlZWs6TUVNRlMuc3RyZWFtX29wcy5sbHNlZWt9fSxmaWxlOntub2RlOntnZXRhdHRyOk1FTUZTLm5vZGVfb3BzLmdldGF0dHIsc2V0YXR0cjpNRU1GUy5ub2RlX29wcy5zZXRhdHRyfSxzdHJlYW06e2xsc2VlazpNRU1GUy5zdHJlYW1fb3BzLmxsc2VlayxyZWFkOk1FTUZTLnN0cmVhbV9vcHMucmVhZCx3cml0ZTpNRU1GUy5zdHJlYW1fb3BzLndyaXRlLG1tYXA6TUVNRlMuc3RyZWFtX29wcy5tbWFwLG1zeW5jOk1FTUZTLnN0cmVhbV9vcHMubXN5bmN9fSxsaW5rOntub2RlOntnZXRhdHRyOk1FTUZTLm5vZGVfb3BzLmdldGF0dHIsc2V0YXR0cjpNRU1GUy5ub2RlX29wcy5zZXRhdHRyLHJlYWRsaW5rOk1FTUZTLm5vZGVfb3BzLnJlYWRsaW5rfSxzdHJlYW06e319LGNocmRldjp7bm9kZTp7Z2V0YXR0cjpNRU1GUy5ub2RlX29wcy5nZXRhdHRyLHNldGF0dHI6TUVNRlMubm9kZV9vcHMuc2V0YXR0cn0sc3RyZWFtOkZTLmNocmRldl9zdHJlYW1fb3BzfX07dmFyIG5vZGU9RlMuY3JlYXRlTm9kZShwYXJlbnQsbmFtZSxtb2RlLGRldik7aWYoRlMuaXNEaXIobm9kZS5tb2RlKSl7bm9kZS5ub2RlX29wcz1NRU1GUy5vcHNfdGFibGUuZGlyLm5vZGU7bm9kZS5zdHJlYW1fb3BzPU1FTUZTLm9wc190YWJsZS5kaXIuc3RyZWFtO25vZGUuY29udGVudHM9e319ZWxzZSBpZihGUy5pc0ZpbGUobm9kZS5tb2RlKSl7bm9kZS5ub2RlX29wcz1NRU1GUy5vcHNfdGFibGUuZmlsZS5ub2RlO25vZGUuc3RyZWFtX29wcz1NRU1GUy5vcHNfdGFibGUuZmlsZS5zdHJlYW07bm9kZS51c2VkQnl0ZXM9MDtub2RlLmNvbnRlbnRzPU1FTUZTLmVtcHR5RmlsZUNvbnRlbnRzPz89bmV3IFVpbnQ4QXJyYXkoMCl9ZWxzZSBpZihGUy5pc0xpbmsobm9kZS5tb2RlKSl7bm9kZS5ub2RlX29wcz1NRU1GUy5vcHNfdGFibGUubGluay5ub2RlO25vZGUuc3RyZWFtX29wcz1NRU1GUy5vcHNfdGFibGUubGluay5zdHJlYW19ZWxzZSBpZihGUy5pc0NocmRldihub2RlLm1vZGUpKXtub2RlLm5vZGVfb3BzPU1FTUZTLm9wc190YWJsZS5jaHJkZXYubm9kZTtub2RlLnN0cmVhbV9vcHM9TUVNRlMub3BzX3RhYmxlLmNocmRldi5zdHJlYW19bm9kZS5hdGltZT1ub2RlLm10aW1lPW5vZGUuY3RpbWU9RGF0ZS5ub3coKTtpZihwYXJlbnQpe3BhcmVudC5jb250ZW50c1tuYW1lXT1ub2RlO3BhcmVudC5hdGltZT1wYXJlbnQubXRpbWU9cGFyZW50LmN0aW1lPW5vZGUuYXRpbWV9cmV0dXJuIG5vZGV9LGdldEZpbGVEYXRhQXNUeXBlZEFycmF5KG5vZGUpe3JldHVybiBub2RlLmNvbnRlbnRzLnN1YmFycmF5KDAsbm9kZS51c2VkQnl0ZXMpfSxleHBhbmRGaWxlU3RvcmFnZShub2RlLG5ld0NhcGFjaXR5KXt2YXIgcHJldkNhcGFjaXR5PW5vZGUuY29udGVudHMubGVuZ3RoO2lmKHByZXZDYXBhY2l0eT49bmV3Q2FwYWNpdHkpcmV0dXJuO3ZhciBDQVBBQ0lUWV9ET1VCTElOR19NQVg9MTAyNCoxMDI0O25ld0NhcGFjaXR5PU1hdGgubWF4KG5ld0NhcGFjaXR5LHByZXZDYXBhY2l0eSoocHJldkNhcGFjaXR5PENBUEFDSVRZX0RPVUJMSU5HX01BWD8yOjEuMTI1KT4+PjApO2lmKHByZXZDYXBhY2l0eSluZXdDYXBhY2l0eT1NYXRoLm1heChuZXdDYXBhY2l0eSwyNTYpO3ZhciBvbGRDb250ZW50cz1NRU1GUy5nZXRGaWxlRGF0YUFzVHlwZWRBcnJheShub2RlKTtub2RlLmNvbnRlbnRzPW5ldyBVaW50OEFycmF5KG5ld0NhcGFjaXR5KTtub2RlLmNvbnRlbnRzLnNldChvbGRDb250ZW50cyl9LHJlc2l6ZUZpbGVTdG9yYWdlKG5vZGUsbmV3U2l6ZSl7aWYobm9kZS51c2VkQnl0ZXM9PW5ld1NpemUpcmV0dXJuO3ZhciBvbGRDb250ZW50cz1ub2RlLmNvbnRlbnRzO25vZGUuY29udGVudHM9bmV3IFVpbnQ4QXJyYXkobmV3U2l6ZSk7bm9kZS5jb250ZW50cy5zZXQob2xkQ29udGVudHMuc3ViYXJyYXkoMCxNYXRoLm1pbihuZXdTaXplLG5vZGUudXNlZEJ5dGVzKSkpO25vZGUudXNlZEJ5dGVzPW5ld1NpemV9LG5vZGVfb3BzOntnZXRhdHRyKG5vZGUpe3ZhciBhdHRyPXt9O2F0dHIuZGV2PUZTLmlzQ2hyZGV2KG5vZGUubW9kZSk/bm9kZS5pZDoxO2F0dHIuaW5vPW5vZGUuaWQ7YXR0ci5tb2RlPW5vZGUubW9kZTthdHRyLm5saW5rPTE7YXR0ci51aWQ9MDthdHRyLmdpZD0wO2F0dHIucmRldj1ub2RlLnJkZXY7aWYoRlMuaXNEaXIobm9kZS5tb2RlKSl7YXR0ci5zaXplPTQwOTZ9ZWxzZSBpZihGUy5pc0ZpbGUobm9kZS5tb2RlKSl7YXR0ci5zaXplPW5vZGUudXNlZEJ5dGVzfWVsc2UgaWYoRlMuaXNMaW5rKG5vZGUubW9kZSkpe2F0dHIuc2l6ZT1ub2RlLmxpbmsubGVuZ3RofWVsc2V7YXR0ci5zaXplPTB9YXR0ci5hdGltZT1uZXcgRGF0ZShub2RlLmF0aW1lKTthdHRyLm10aW1lPW5ldyBEYXRlKG5vZGUubXRpbWUpO2F0dHIuY3RpbWU9bmV3IERhdGUobm9kZS5jdGltZSk7YXR0ci5ibGtzaXplPTQwOTY7YXR0ci5ibG9ja3M9TWF0aC5jZWlsKGF0dHIuc2l6ZS9hdHRyLmJsa3NpemUpO3JldHVybiBhdHRyfSxzZXRhdHRyKG5vZGUsYXR0cil7Zm9yKGNvbnN0IGtleSBvZlsibW9kZSIsImF0aW1lIiwibXRpbWUiLCJjdGltZSJdKXtpZihhdHRyW2tleV0hPW51bGwpe25vZGVba2V5XT1hdHRyW2tleV19fWlmKGF0dHIuc2l6ZSE9PXVuZGVmaW5lZCl7TUVNRlMucmVzaXplRmlsZVN0b3JhZ2Uobm9kZSxhdHRyLnNpemUpfX0sbG9va3VwKHBhcmVudCxuYW1lKXtpZighTUVNRlMuZG9lc05vdEV4aXN0RXJyb3Ipe01FTUZTLmRvZXNOb3RFeGlzdEVycm9yPW5ldyBGUy5FcnJub0Vycm9yKDQ0KTtNRU1GUy5kb2VzTm90RXhpc3RFcnJvci5zdGFjaz0iPGdlbmVyaWMgZXJyb3IsIG5vIHN0YWNrPiJ9dGhyb3cgTUVNRlMuZG9lc05vdEV4aXN0RXJyb3J9LG1rbm9kKHBhcmVudCxuYW1lLG1vZGUsZGV2KXtyZXR1cm4gTUVNRlMuY3JlYXRlTm9kZShwYXJlbnQsbmFtZSxtb2RlLGRldil9LHJlbmFtZShvbGRfbm9kZSxuZXdfZGlyLG5ld19uYW1lKXt2YXIgbmV3X25vZGU7dHJ5e25ld19ub2RlPUZTLmxvb2t1cE5vZGUobmV3X2RpcixuZXdfbmFtZSl9Y2F0Y2goZSl7fWlmKG5ld19ub2RlKXtpZihGUy5pc0RpcihvbGRfbm9kZS5tb2RlKSl7Zm9yKHZhciBpIGluIG5ld19ub2RlLmNvbnRlbnRzKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig1NSl9fUZTLmhhc2hSZW1vdmVOb2RlKG5ld19ub2RlKX1kZWxldGUgb2xkX25vZGUucGFyZW50LmNvbnRlbnRzW29sZF9ub2RlLm5hbWVdO25ld19kaXIuY29udGVudHNbbmV3X25hbWVdPW9sZF9ub2RlO29sZF9ub2RlLm5hbWU9bmV3X25hbWU7bmV3X2Rpci5jdGltZT1uZXdfZGlyLm10aW1lPW9sZF9ub2RlLnBhcmVudC5jdGltZT1vbGRfbm9kZS5wYXJlbnQubXRpbWU9RGF0ZS5ub3coKX0sdW5saW5rKHBhcmVudCxuYW1lKXtkZWxldGUgcGFyZW50LmNvbnRlbnRzW25hbWVdO3BhcmVudC5jdGltZT1wYXJlbnQubXRpbWU9RGF0ZS5ub3coKX0scm1kaXIocGFyZW50LG5hbWUpe3ZhciBub2RlPUZTLmxvb2t1cE5vZGUocGFyZW50LG5hbWUpO2Zvcih2YXIgaSBpbiBub2RlLmNvbnRlbnRzKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig1NSl9ZGVsZXRlIHBhcmVudC5jb250ZW50c1tuYW1lXTtwYXJlbnQuY3RpbWU9cGFyZW50Lm10aW1lPURhdGUubm93KCl9LHJlYWRkaXIobm9kZSl7cmV0dXJuWyIuIiwiLi4iLC4uLk9iamVjdC5rZXlzKG5vZGUuY29udGVudHMpXX0sc3ltbGluayhwYXJlbnQsbmV3bmFtZSxvbGRwYXRoKXt2YXIgbm9kZT1NRU1GUy5jcmVhdGVOb2RlKHBhcmVudCxuZXduYW1lLDUxMXw0MDk2MCwwKTtub2RlLmxpbms9b2xkcGF0aDtyZXR1cm4gbm9kZX0scmVhZGxpbmsobm9kZSl7aWYoIUZTLmlzTGluayhub2RlLm1vZGUpKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyOCl9cmV0dXJuIG5vZGUubGlua319LHN0cmVhbV9vcHM6e3JlYWQoc3RyZWFtLGJ1ZmZlcixvZmZzZXQsbGVuZ3RoLHBvc2l0aW9uKXt2YXIgY29udGVudHM9c3RyZWFtLm5vZGUuY29udGVudHM7aWYocG9zaXRpb24+PXN0cmVhbS5ub2RlLnVzZWRCeXRlcylyZXR1cm4gMDt2YXIgc2l6ZT1NYXRoLm1pbihzdHJlYW0ubm9kZS51c2VkQnl0ZXMtcG9zaXRpb24sbGVuZ3RoKTtidWZmZXIuc2V0KGNvbnRlbnRzLnN1YmFycmF5KHBvc2l0aW9uLHBvc2l0aW9uK3NpemUpLG9mZnNldCk7cmV0dXJuIHNpemV9LHdyaXRlKHN0cmVhbSxidWZmZXIsb2Zmc2V0LGxlbmd0aCxwb3NpdGlvbixjYW5Pd24pe2lmKGJ1ZmZlci5idWZmZXI9PT1IRUFQOC5idWZmZXIpe2Nhbk93bj1mYWxzZX1pZighbGVuZ3RoKXJldHVybiAwO3ZhciBub2RlPXN0cmVhbS5ub2RlO25vZGUubXRpbWU9bm9kZS5jdGltZT1EYXRlLm5vdygpO2lmKGNhbk93bil7bm9kZS5jb250ZW50cz1idWZmZXIuc3ViYXJyYXkob2Zmc2V0LG9mZnNldCtsZW5ndGgpO25vZGUudXNlZEJ5dGVzPWxlbmd0aH1lbHNlIGlmKCFub2RlLnVzZWRCeXRlcyYmIXBvc2l0aW9uKXtub2RlLmNvbnRlbnRzPWJ1ZmZlci5zbGljZShvZmZzZXQsb2Zmc2V0K2xlbmd0aCk7bm9kZS51c2VkQnl0ZXM9bGVuZ3RofWVsc2V7TUVNRlMuZXhwYW5kRmlsZVN0b3JhZ2Uobm9kZSxwb3NpdGlvbitsZW5ndGgpO25vZGUuY29udGVudHMuc2V0KGJ1ZmZlci5zdWJhcnJheShvZmZzZXQsb2Zmc2V0K2xlbmd0aCkscG9zaXRpb24pO25vZGUudXNlZEJ5dGVzPU1hdGgubWF4KG5vZGUudXNlZEJ5dGVzLHBvc2l0aW9uK2xlbmd0aCl9cmV0dXJuIGxlbmd0aH0sbGxzZWVrKHN0cmVhbSxvZmZzZXQsd2hlbmNlKXt2YXIgcG9zaXRpb249b2Zmc2V0O2lmKHdoZW5jZT09PTEpe3Bvc2l0aW9uKz1zdHJlYW0ucG9zaXRpb259ZWxzZSBpZih3aGVuY2U9PT0yKXtpZihGUy5pc0ZpbGUoc3RyZWFtLm5vZGUubW9kZSkpe3Bvc2l0aW9uKz1zdHJlYW0ubm9kZS51c2VkQnl0ZXN9fWlmKHBvc2l0aW9uPDApe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX1yZXR1cm4gcG9zaXRpb259LG1tYXAoc3RyZWFtLGxlbmd0aCxwb3NpdGlvbixwcm90LGZsYWdzKXtpZighRlMuaXNGaWxlKHN0cmVhbS5ub2RlLm1vZGUpKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig0Myl9dmFyIHB0cjt2YXIgYWxsb2NhdGVkO3ZhciBjb250ZW50cz1zdHJlYW0ubm9kZS5jb250ZW50cztpZighKGZsYWdzJjIpJiZjb250ZW50cy5idWZmZXI9PT1IRUFQOC5idWZmZXIpe2FsbG9jYXRlZD1mYWxzZTtwdHI9Y29udGVudHMuYnl0ZU9mZnNldH1lbHNle2FsbG9jYXRlZD10cnVlO3B0cj1tbWFwQWxsb2MobGVuZ3RoKTtpZighcHRyKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig0OCl9aWYoY29udGVudHMpe2lmKHBvc2l0aW9uPjB8fHBvc2l0aW9uK2xlbmd0aDxjb250ZW50cy5sZW5ndGgpe2lmKGNvbnRlbnRzLnN1YmFycmF5KXtjb250ZW50cz1jb250ZW50cy5zdWJhcnJheShwb3NpdGlvbixwb3NpdGlvbitsZW5ndGgpfWVsc2V7Y29udGVudHM9QXJyYXkucHJvdG90eXBlLnNsaWNlLmNhbGwoY29udGVudHMscG9zaXRpb24scG9zaXRpb24rbGVuZ3RoKX19SEVBUDguc2V0KGNvbnRlbnRzLHB0cil9fXJldHVybntwdHIsYWxsb2NhdGVkfX0sbXN5bmMoc3RyZWFtLGJ1ZmZlcixvZmZzZXQsbGVuZ3RoLG1tYXBGbGFncyl7TUVNRlMuc3RyZWFtX29wcy53cml0ZShzdHJlYW0sYnVmZmVyLDAsbGVuZ3RoLG9mZnNldCxmYWxzZSk7cmV0dXJuIDB9fX07dmFyIEZTX21vZGVTdHJpbmdUb0ZsYWdzPXN0cj0+e2lmKHR5cGVvZiBzdHIhPSJzdHJpbmciKXJldHVybiBzdHI7dmFyIGZsYWdNb2Rlcz17cjowLCJyKyI6Mix3OjUxMnw2NHwxLCJ3KyI6NTEyfDY0fDIsYToxMDI0fDY0fDEsImErIjoxMDI0fDY0fDJ9O3ZhciBmbGFncz1mbGFnTW9kZXNbc3RyXTtpZih0eXBlb2YgZmxhZ3M9PSJ1bmRlZmluZWQiKXt0aHJvdyBuZXcgRXJyb3IoYFVua25vd24gZmlsZSBvcGVuIG1vZGU6ICR7c3RyfWApfXJldHVybiBmbGFnc307dmFyIEZTX2ZpbGVEYXRhVG9UeXBlZEFycmF5PWRhdGE9PntpZih0eXBlb2YgZGF0YT09InN0cmluZyIpe2RhdGE9aW50QXJyYXlGcm9tU3RyaW5nKGRhdGEsdHJ1ZSl9aWYoIWRhdGEuc3ViYXJyYXkpe2RhdGE9bmV3IFVpbnQ4QXJyYXkoZGF0YSl9cmV0dXJuIGRhdGF9O3ZhciBGU19nZXRNb2RlPShjYW5SZWFkLGNhbldyaXRlKT0+e3ZhciBtb2RlPTA7aWYoY2FuUmVhZCltb2RlfD0yOTJ8NzM7aWYoY2FuV3JpdGUpbW9kZXw9MTQ2O3JldHVybiBtb2RlfTt2YXIgYXN5bmNMb2FkPWFzeW5jIHVybD0+e3ZhciBhcnJheUJ1ZmZlcj1hd2FpdCByZWFkQXN5bmModXJsKTtyZXR1cm4gbmV3IFVpbnQ4QXJyYXkoYXJyYXlCdWZmZXIpfTt2YXIgRlNfY3JlYXRlRGF0YUZpbGU9KC4uLmFyZ3MpPT5GUy5jcmVhdGVEYXRhRmlsZSguLi5hcmdzKTt2YXIgZ2V0VW5pcXVlUnVuRGVwZW5kZW5jeT1pZD0+aWQ7dmFyIGRlcGVuZGVuY2llc1Byb21pc2U9bnVsbDt2YXIgcmVzb2x2ZVJ1bkRlcGVuZGVuY2llcz1hc3luYygpPT5kZXBlbmRlbmNpZXNQcm9taXNlO3ZhciBydW5EZXBlbmRlbmNpZXM9MDt2YXIgZGVwZW5kZW5jaWVzUHJvbWlzZVJlc29sdmU9bnVsbDt2YXIgcmVtb3ZlUnVuRGVwZW5kZW5jeT1pZD0+e3J1bkRlcGVuZGVuY2llcy0tO01vZHVsZVsibW9uaXRvclJ1bkRlcGVuZGVuY2llcyJdPy4ocnVuRGVwZW5kZW5jaWVzKTtpZighcnVuRGVwZW5kZW5jaWVzKXtkZXBlbmRlbmNpZXNQcm9taXNlUmVzb2x2ZSgpfX07dmFyIGFkZFJ1bkRlcGVuZGVuY3k9aWQ9PntpZighcnVuRGVwZW5kZW5jaWVzKXtkZXBlbmRlbmNpZXNQcm9taXNlPW5ldyBQcm9taXNlKHJlc29sdmU9PmRlcGVuZGVuY2llc1Byb21pc2VSZXNvbHZlPXJlc29sdmUpfXJ1bkRlcGVuZGVuY2llcysrO01vZHVsZVsibW9uaXRvclJ1bkRlcGVuZGVuY2llcyJdPy4ocnVuRGVwZW5kZW5jaWVzKX07dmFyIHByZWxvYWRQbHVnaW5zPVtdO3ZhciBGU19oYW5kbGVkQnlQcmVsb2FkUGx1Z2luPWFzeW5jKGJ5dGVBcnJheSxmdWxsbmFtZSk9PntpZih0eXBlb2YgQnJvd3NlciE9InVuZGVmaW5lZCIpQnJvd3Nlci5pbml0KCk7Zm9yKHZhciBwbHVnaW4gb2YgcHJlbG9hZFBsdWdpbnMpe2lmKHBsdWdpblsiY2FuSGFuZGxlIl0oZnVsbG5hbWUpKXtyZXR1cm4gcGx1Z2luWyJoYW5kbGUiXShieXRlQXJyYXksZnVsbG5hbWUpfX1yZXR1cm4gYnl0ZUFycmF5fTt2YXIgRlNfcHJlbG9hZEZpbGU9YXN5bmMocGFyZW50LG5hbWUsdXJsLGNhblJlYWQsY2FuV3JpdGUsZG9udENyZWF0ZUZpbGUsY2FuT3duLHByZUZpbmlzaCk9Pnt2YXIgZnVsbG5hbWU9bmFtZT9QQVRIX0ZTLnJlc29sdmUoUEFUSC5qb2luMihwYXJlbnQsbmFtZSkpOnBhcmVudDt2YXIgZGVwPWdldFVuaXF1ZVJ1bkRlcGVuZGVuY3koYGNwICR7ZnVsbG5hbWV9YCk7YWRkUnVuRGVwZW5kZW5jeShkZXApO3RyeXt2YXIgYnl0ZUFycmF5PXVybDtpZih0eXBlb2YgdXJsPT0ic3RyaW5nIil7Ynl0ZUFycmF5PWF3YWl0IGFzeW5jTG9hZCh1cmwpfWJ5dGVBcnJheT1hd2FpdCBGU19oYW5kbGVkQnlQcmVsb2FkUGx1Z2luKGJ5dGVBcnJheSxmdWxsbmFtZSk7cHJlRmluaXNoPy4oKTtpZighZG9udENyZWF0ZUZpbGUpe0ZTX2NyZWF0ZURhdGFGaWxlKHBhcmVudCxuYW1lLGJ5dGVBcnJheSxjYW5SZWFkLGNhbldyaXRlLGNhbk93bil9fWZpbmFsbHl7cmVtb3ZlUnVuRGVwZW5kZW5jeShkZXApfX07dmFyIEZTX2NyZWF0ZVByZWxvYWRlZEZpbGU9KHBhcmVudCxuYW1lLHVybCxjYW5SZWFkLGNhbldyaXRlLG9ubG9hZCxvbmVycm9yLGRvbnRDcmVhdGVGaWxlLGNhbk93bixwcmVGaW5pc2gpPT57RlNfcHJlbG9hZEZpbGUocGFyZW50LG5hbWUsdXJsLGNhblJlYWQsY2FuV3JpdGUsZG9udENyZWF0ZUZpbGUsY2FuT3duLHByZUZpbmlzaCkudGhlbihvbmxvYWQpLmNhdGNoKG9uZXJyb3IpfTt2YXIgRlM9e3Jvb3Q6bnVsbCxtb3VudHM6W10sZGV2aWNlczp7fSxzdHJlYW1zOltdLG5leHRJbm9kZToxLG5hbWVUYWJsZTpudWxsLGN1cnJlbnRQYXRoOiIvIixpbml0aWFsaXplZDpmYWxzZSxpZ25vcmVQZXJtaXNzaW9uczp0cnVlLGZpbGVzeXN0ZW1zOm51bGwsc3luY0ZTUmVxdWVzdHM6MCxFcnJub0Vycm9yOmNsYXNze25hbWU9IkVycm5vRXJyb3IiO2NvbnN0cnVjdG9yKGVycm5vKXt0aGlzLmVycm5vPWVycm5vfX0sRlNTdHJlYW06Y2xhc3N7c2hhcmVkPXt9O2dldCBvYmplY3QoKXtyZXR1cm4gdGhpcy5ub2RlfXNldCBvYmplY3QodmFsKXt0aGlzLm5vZGU9dmFsfWdldCBpc1JlYWQoKXtyZXR1cm4odGhpcy5mbGFncyYyMDk3MTU1KSE9PTF9Z2V0IGlzV3JpdGUoKXtyZXR1cm4odGhpcy5mbGFncyYyMDk3MTU1KSE9PTB9Z2V0IGlzQXBwZW5kKCl7cmV0dXJuIHRoaXMuZmxhZ3MmMTAyNH1nZXQgZmxhZ3MoKXtyZXR1cm4gdGhpcy5zaGFyZWQuZmxhZ3N9c2V0IGZsYWdzKHZhbCl7dGhpcy5zaGFyZWQuZmxhZ3M9dmFsfWdldCBwb3NpdGlvbigpe3JldHVybiB0aGlzLnNoYXJlZC5wb3NpdGlvbn1zZXQgcG9zaXRpb24odmFsKXt0aGlzLnNoYXJlZC5wb3NpdGlvbj12YWx9fSxGU05vZGU6Y2xhc3N7bm9kZV9vcHM9e307c3RyZWFtX29wcz17fTtyZWFkTW9kZT0yOTJ8NzM7d3JpdGVNb2RlPTE0Njttb3VudGVkPW51bGw7Y29uc3RydWN0b3IocGFyZW50LG5hbWUsbW9kZSxyZGV2KXtpZighcGFyZW50KXtwYXJlbnQ9dGhpc310aGlzLnBhcmVudD1wYXJlbnQ7dGhpcy5tb3VudD1wYXJlbnQubW91bnQ7dGhpcy5pZD1GUy5uZXh0SW5vZGUrKzt0aGlzLm5hbWU9bmFtZTt0aGlzLm1vZGU9bW9kZTt0aGlzLnJkZXY9cmRldjt0aGlzLmF0aW1lPXRoaXMubXRpbWU9dGhpcy5jdGltZT1EYXRlLm5vdygpfWdldCByZWFkKCl7cmV0dXJuKHRoaXMubW9kZSZ0aGlzLnJlYWRNb2RlKT09PXRoaXMucmVhZE1vZGV9c2V0IHJlYWQodmFsKXt2YWw/dGhpcy5tb2RlfD10aGlzLnJlYWRNb2RlOnRoaXMubW9kZSY9fnRoaXMucmVhZE1vZGV9Z2V0IHdyaXRlKCl7cmV0dXJuKHRoaXMubW9kZSZ0aGlzLndyaXRlTW9kZSk9PT10aGlzLndyaXRlTW9kZX1zZXQgd3JpdGUodmFsKXt2YWw/dGhpcy5tb2RlfD10aGlzLndyaXRlTW9kZTp0aGlzLm1vZGUmPX50aGlzLndyaXRlTW9kZX1nZXQgaXNGb2xkZXIoKXtyZXR1cm4gRlMuaXNEaXIodGhpcy5tb2RlKX1nZXQgaXNEZXZpY2UoKXtyZXR1cm4gRlMuaXNDaHJkZXYodGhpcy5tb2RlKX1hZGRMaXN0ZW5lcihjYixleGNsdXNpdmU9ZmFsc2Upe3ZhciBlbnRyeT17Y2IsZXhjbHVzaXZlfTt2YXIgbGlzdGVuZXJzPXRoaXMubGlzdGVuZXJzPz89bmV3IFNldDtsaXN0ZW5lcnMuYWRkKGVudHJ5KTtyZXR1cm57bGlzdGVuZXJzLGVudHJ5fX1ub3RpZnlMaXN0ZW5lcnMoZmxhZ3Mpe2lmKCF0aGlzLmxpc3RlbmVycylyZXR1cm47dmFyIGV4Y2w7Zm9yKHZhciBlbnRyeSBvZiB0aGlzLmxpc3RlbmVycyl7aWYoZW50cnkuZXhjbHVzaXZlKShleGNsfHw9W10pLnB1c2goZW50cnkpO2Vsc2UgZW50cnkuY2IoZmxhZ3MpfWlmKGV4Y2wpe3ZhciBpPSh0aGlzLmV4Y2xUdXJufHwwKSVleGNsLmxlbmd0aDt0aGlzLmV4Y2xUdXJuPWkrMTtleGNsW2ldLmNiKGZsYWdzKX19fSxsb29rdXBQYXRoKHBhdGgsb3B0cz17fSl7aWYoIXBhdGgpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDQ0KX1vcHRzLmZvbGxvd19tb3VudD8/PXRydWU7aWYoIVBBVEguaXNBYnMocGF0aCkpe3BhdGg9RlMuY3dkKCkrIi8iK3BhdGh9bGlua2xvb3A6Zm9yKHZhciBubGlua3M9MDtubGlua3M8NDA7bmxpbmtzKyspe3ZhciBwYXJ0cz1wYXRoLnNwbGl0KCIvIikuZmlsdGVyKHA9PiEhcCk7dmFyIGN1cnJlbnQ9RlMucm9vdDt2YXIgY3VycmVudF9wYXRoPSIvIjtmb3IodmFyIGk9MDtpPHBhcnRzLmxlbmd0aDtpKyspe3ZhciBpc2xhc3Q9aT09PXBhcnRzLmxlbmd0aC0xO2lmKGlzbGFzdCYmb3B0cy5wYXJlbnQpe2JyZWFrfWlmKHBhcnRzW2ldPT09Ii4iKXtjb250aW51ZX1pZihwYXJ0c1tpXT09PSIuLiIpe2N1cnJlbnRfcGF0aD1QQVRILmRpcm5hbWUoY3VycmVudF9wYXRoKTtpZihGUy5pc1Jvb3QoY3VycmVudCkpe3BhdGg9Y3VycmVudF9wYXRoKyIvIitwYXJ0cy5zbGljZShpKzEpLmpvaW4oIi8iKTtubGlua3MtLTtjb250aW51ZSBsaW5rbG9vcH1lbHNle2N1cnJlbnQ9Y3VycmVudC5wYXJlbnR9Y29udGludWV9Y3VycmVudF9wYXRoPVBBVEguam9pbjIoY3VycmVudF9wYXRoLHBhcnRzW2ldKTt0cnl7Y3VycmVudD1GUy5sb29rdXBOb2RlKGN1cnJlbnQscGFydHNbaV0pfWNhdGNoKGUpe2lmKGU/LmVycm5vPT09NDQmJmlzbGFzdCYmb3B0cy5ub2VudF9va2F5KXtyZXR1cm57cGF0aDpjdXJyZW50X3BhdGh9fXRocm93IGV9aWYoRlMuaXNNb3VudHBvaW50KGN1cnJlbnQpJiYoIWlzbGFzdHx8b3B0cy5mb2xsb3dfbW91bnQpKXtjdXJyZW50PWN1cnJlbnQubW91bnRlZC5yb290fWlmKEZTLmlzTGluayhjdXJyZW50Lm1vZGUpJiYoIWlzbGFzdHx8b3B0cy5mb2xsb3cpKXtpZighY3VycmVudC5ub2RlX29wcy5yZWFkbGluayl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNTIpfXZhciBsaW5rPWN1cnJlbnQubm9kZV9vcHMucmVhZGxpbmsoY3VycmVudCk7aWYoIVBBVEguaXNBYnMobGluaykpe2xpbms9UEFUSC5kaXJuYW1lKGN1cnJlbnRfcGF0aCkrIi8iK2xpbmt9cGF0aD1saW5rKyIvIitwYXJ0cy5zbGljZShpKzEpLmpvaW4oIi8iKTtjb250aW51ZSBsaW5rbG9vcH19cmV0dXJue3BhdGg6Y3VycmVudF9wYXRoLG5vZGU6Y3VycmVudH19dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoMzIpfSxnZXRQYXRoKG5vZGUpe3ZhciBwYXRoO3doaWxlKHRydWUpe2lmKEZTLmlzUm9vdChub2RlKSl7dmFyIG1vdW50PW5vZGUubW91bnQubW91bnRwb2ludDtpZighcGF0aClyZXR1cm4gbW91bnQ7cmV0dXJuIG1vdW50W21vdW50Lmxlbmd0aC0xXSE9PSIvIj9gJHttb3VudH0vJHtwYXRofWA6bW91bnQrcGF0aH1wYXRoPXBhdGg/YCR7bm9kZS5uYW1lfS8ke3BhdGh9YDpub2RlLm5hbWU7bm9kZT1ub2RlLnBhcmVudH19LGhhc2hOYW1lKHBhcmVudGlkLG5hbWUpe3ZhciBoYXNoPTA7Zm9yKHZhciBpPTA7aTxuYW1lLmxlbmd0aDtpKyspe2hhc2g9KGhhc2g8PDUpLWhhc2grbmFtZS5jaGFyQ29kZUF0KGkpfDB9cmV0dXJuKHBhcmVudGlkK2hhc2g+Pj4wKSVGUy5uYW1lVGFibGUubGVuZ3RofSxoYXNoQWRkTm9kZShub2RlKXt2YXIgaGFzaD1GUy5oYXNoTmFtZShub2RlLnBhcmVudC5pZCxub2RlLm5hbWUpO25vZGUubmFtZV9uZXh0PUZTLm5hbWVUYWJsZVtoYXNoXTtGUy5uYW1lVGFibGVbaGFzaF09bm9kZX0saGFzaFJlbW92ZU5vZGUobm9kZSl7dmFyIGhhc2g9RlMuaGFzaE5hbWUobm9kZS5wYXJlbnQuaWQsbm9kZS5uYW1lKTtpZihGUy5uYW1lVGFibGVbaGFzaF09PT1ub2RlKXtGUy5uYW1lVGFibGVbaGFzaF09bm9kZS5uYW1lX25leHR9ZWxzZXt2YXIgY3VycmVudD1GUy5uYW1lVGFibGVbaGFzaF07d2hpbGUoY3VycmVudCl7aWYoY3VycmVudC5uYW1lX25leHQ9PT1ub2RlKXtjdXJyZW50Lm5hbWVfbmV4dD1ub2RlLm5hbWVfbmV4dDticmVha31jdXJyZW50PWN1cnJlbnQubmFtZV9uZXh0fX19LGxvb2t1cE5vZGUocGFyZW50LG5hbWUpe3ZhciBlcnJDb2RlPUZTLm1heUxvb2t1cChwYXJlbnQpO2lmKGVyckNvZGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKGVyckNvZGUpfXZhciBoYXNoPUZTLmhhc2hOYW1lKHBhcmVudC5pZCxuYW1lKTtmb3IodmFyIG5vZGU9RlMubmFtZVRhYmxlW2hhc2hdO25vZGU7bm9kZT1ub2RlLm5hbWVfbmV4dCl7dmFyIG5vZGVOYW1lPW5vZGUubmFtZTtpZihub2RlLnBhcmVudC5pZD09PXBhcmVudC5pZCYmbm9kZU5hbWU9PT1uYW1lKXtyZXR1cm4gbm9kZX19cmV0dXJuIEZTLmxvb2t1cChwYXJlbnQsbmFtZSl9LGNyZWF0ZU5vZGUocGFyZW50LG5hbWUsbW9kZSxyZGV2KXt2YXIgbm9kZT1uZXcgRlMuRlNOb2RlKHBhcmVudCxuYW1lLG1vZGUscmRldik7RlMuaGFzaEFkZE5vZGUobm9kZSk7cmV0dXJuIG5vZGV9LGRlc3Ryb3lOb2RlKG5vZGUpe0ZTLmhhc2hSZW1vdmVOb2RlKG5vZGUpfSxpc1Jvb3Qobm9kZSl7cmV0dXJuIG5vZGU9PT1ub2RlLnBhcmVudH0saXNNb3VudHBvaW50KG5vZGUpe3JldHVybiEhbm9kZS5tb3VudGVkfSxpc0ZpbGUobW9kZSl7cmV0dXJuKG1vZGUmNjE0NDApPT09MzI3Njh9LGlzRGlyKG1vZGUpe3JldHVybihtb2RlJjYxNDQwKT09PTE2Mzg0fSxpc0xpbmsobW9kZSl7cmV0dXJuKG1vZGUmNjE0NDApPT09NDA5NjB9LGlzQ2hyZGV2KG1vZGUpe3JldHVybihtb2RlJjYxNDQwKT09PTgxOTJ9LGlzQmxrZGV2KG1vZGUpe3JldHVybihtb2RlJjYxNDQwKT09PTI0NTc2fSxpc0ZJRk8obW9kZSl7cmV0dXJuKG1vZGUmNjE0NDApPT09NDA5Nn0saXNTb2NrZXQobW9kZSl7cmV0dXJuKG1vZGUmNDkxNTIpPT09NDkxNTJ9LGZsYWdzVG9QZXJtaXNzaW9uU3RyaW5nKGZsYWcpe3ZhciBwZXJtcz1bInIiLCJ3IiwicnciXVtmbGFnJjNdO2lmKGZsYWcmNTEyKXtwZXJtcys9IncifXJldHVybiBwZXJtc30sbm9kZVBlcm1pc3Npb25zKG5vZGUscGVybXMpe2lmKEZTLmlnbm9yZVBlcm1pc3Npb25zKXtyZXR1cm4gMH1pZihwZXJtcy5pbmNsdWRlcygiciIpJiYhKG5vZGUubW9kZSYyOTIpKXtyZXR1cm4gMn1pZihwZXJtcy5pbmNsdWRlcygidyIpJiYhKG5vZGUubW9kZSYxNDYpKXtyZXR1cm4gMn1pZihwZXJtcy5pbmNsdWRlcygieCIpJiYhKG5vZGUubW9kZSY3Mykpe3JldHVybiAyfXJldHVybiAwfSxtYXlMb29rdXAoZGlyKXtpZighRlMuaXNEaXIoZGlyLm1vZGUpKXJldHVybiA1NDt2YXIgZXJyQ29kZT1GUy5ub2RlUGVybWlzc2lvbnMoZGlyLCJ4Iik7aWYoZXJyQ29kZSlyZXR1cm4gZXJyQ29kZTtpZighZGlyLm5vZGVfb3BzLmxvb2t1cClyZXR1cm4gMjtyZXR1cm4gMH0sbWF5Q3JlYXRlKGRpcixuYW1lKXtpZighRlMuaXNEaXIoZGlyLm1vZGUpKXtyZXR1cm4gNTR9dHJ5e3ZhciBub2RlPUZTLmxvb2t1cE5vZGUoZGlyLG5hbWUpO3JldHVybiAyMH1jYXRjaChlKXt9cmV0dXJuIEZTLm5vZGVQZXJtaXNzaW9ucyhkaXIsInd4Iil9LG1heURlbGV0ZShkaXIsbmFtZSxpc2Rpcil7dmFyIG5vZGU7dHJ5e25vZGU9RlMubG9va3VwTm9kZShkaXIsbmFtZSl9Y2F0Y2goZSl7cmV0dXJuIGUuZXJybm99dmFyIGVyckNvZGU9RlMubm9kZVBlcm1pc3Npb25zKGRpciwid3giKTtpZihlcnJDb2RlKXtyZXR1cm4gZXJyQ29kZX1pZihpc2Rpcil7aWYoIUZTLmlzRGlyKG5vZGUubW9kZSkpe3JldHVybiA1NH1pZihGUy5pc1Jvb3Qobm9kZSl8fEZTLmdldFBhdGgobm9kZSk9PT1GUy5jd2QoKSl7cmV0dXJuIDEwfX1lbHNlIGlmKEZTLmlzRGlyKG5vZGUubW9kZSkpe3JldHVybiAzMX1yZXR1cm4gMH0sbWF5T3Blbihub2RlLGZsYWdzKXtpZighbm9kZSl7cmV0dXJuIDQ0fWlmKEZTLmlzTGluayhub2RlLm1vZGUpKXtyZXR1cm4gMzJ9dmFyIG1vZGU9RlMuZmxhZ3NUb1Blcm1pc3Npb25TdHJpbmcoZmxhZ3MpO2lmKEZTLmlzRGlyKG5vZGUubW9kZSkpe2lmKG1vZGUhPT0iciJ8fGZsYWdzJig1MTJ8NjQpKXtyZXR1cm4gMzF9fXJldHVybiBGUy5ub2RlUGVybWlzc2lvbnMobm9kZSxtb2RlKX0sY2hlY2tPcEV4aXN0cyhvcCxlcnIpe2lmKCFvcCl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoZXJyKX1yZXR1cm4gb3B9LE1BWF9PUEVOX0ZEUzo0MDk2LG5leHRmZCgpe2Zvcih2YXIgZmQ9MDtmZDw9RlMuTUFYX09QRU5fRkRTO2ZkKyspe2lmKCFGUy5zdHJlYW1zW2ZkXSl7cmV0dXJuIGZkfX10aHJvdyBuZXcgRlMuRXJybm9FcnJvcigzMyl9LGdldFN0cmVhbUNoZWNrZWQoZmQpe3ZhciBzdHJlYW09RlMuZ2V0U3RyZWFtKGZkKTtpZighc3RyZWFtKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig4KX1yZXR1cm4gc3RyZWFtfSxnZXRTdHJlYW06ZmQ9PkZTLnN0cmVhbXNbZmRdLGNyZWF0ZVN0cmVhbShzdHJlYW0sZmQ9LTEpe3N0cmVhbT1PYmplY3QuYXNzaWduKG5ldyBGUy5GU1N0cmVhbSxzdHJlYW0pO2lmKGZkPT0tMSl7ZmQ9RlMubmV4dGZkKCl9c3RyZWFtLmZkPWZkO0ZTLnN0cmVhbXNbZmRdPXN0cmVhbTtyZXR1cm4gc3RyZWFtfSxjbG9zZVN0cmVhbShmZCl7RlMuc3RyZWFtc1tmZF09bnVsbH0sZHVwU3RyZWFtKG9yaWdTdHJlYW0sZmQ9LTEpe3ZhciBzdHJlYW09RlMuY3JlYXRlU3RyZWFtKG9yaWdTdHJlYW0sZmQpO3N0cmVhbS5zdHJlYW1fb3BzPy5kdXA/LihzdHJlYW0pO3JldHVybiBzdHJlYW19LGRvU2V0QXR0cihzdHJlYW0sbm9kZSxhdHRyKXt2YXIgc2V0YXR0cj1zdHJlYW0/LnN0cmVhbV9vcHMuc2V0YXR0cjt2YXIgYXJnPXNldGF0dHI/c3RyZWFtOm5vZGU7c2V0YXR0cj8/PW5vZGUubm9kZV9vcHMuc2V0YXR0cjtGUy5jaGVja09wRXhpc3RzKHNldGF0dHIsNjMpO3RyeXtzZXRhdHRyKGFyZyxhdHRyKX1jYXRjaChlKXtpZihlIGluc3RhbmNlb2YgUmFuZ2VFcnJvcil7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoMjIpfXRocm93IGV9fSxjaHJkZXZfc3RyZWFtX29wczp7b3BlbihzdHJlYW0pe3ZhciBkZXZpY2U9RlMuZ2V0RGV2aWNlKHN0cmVhbS5ub2RlLnJkZXYpO3N0cmVhbS5zdHJlYW1fb3BzPWRldmljZS5zdHJlYW1fb3BzO3N0cmVhbS5zdHJlYW1fb3BzLm9wZW4/LihzdHJlYW0pfSxsbHNlZWsoKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig3MCl9fSxtYWpvcjpkZXY9PmRldj4+OCxtaW5vcjpkZXY9PmRldiYyNTUsbWFrZWRldjoobWEsbWkpPT5tYTw8OHxtaSxyZWdpc3RlckRldmljZShkZXYsb3BzKXtGUy5kZXZpY2VzW2Rldl09e3N0cmVhbV9vcHM6b3BzfX0sZ2V0RGV2aWNlOmRldj0+RlMuZGV2aWNlc1tkZXZdLGdldE1vdW50cyhtb3VudCl7dmFyIG1vdW50cz1bXTt2YXIgY2hlY2s9W21vdW50XTt3aGlsZShjaGVjay5sZW5ndGgpe3ZhciBtPWNoZWNrLnBvcCgpO21vdW50cy5wdXNoKG0pO2NoZWNrLnB1c2goLi4ubS5tb3VudHMpfXJldHVybiBtb3VudHN9LHN5bmNmcyhwb3B1bGF0ZSxjYWxsYmFjayl7aWYodHlwZW9mIHBvcHVsYXRlPT0iZnVuY3Rpb24iKXtjYWxsYmFjaz1wb3B1bGF0ZTtwb3B1bGF0ZT1mYWxzZX1GUy5zeW5jRlNSZXF1ZXN0cysrO2lmKEZTLnN5bmNGU1JlcXVlc3RzPjEpe2Vycihgd2FybmluZzogJHtGUy5zeW5jRlNSZXF1ZXN0c30gRlMuc3luY2ZzIG9wZXJhdGlvbnMgaW4gZmxpZ2h0IGF0IG9uY2UsIHByb2JhYmx5IGp1c3QgZG9pbmcgZXh0cmEgd29ya2ApfXZhciBtb3VudHM9RlMuZ2V0TW91bnRzKEZTLnJvb3QubW91bnQpO3ZhciBjb21wbGV0ZWQ9MDtmdW5jdGlvbiBkb0NhbGxiYWNrKGVyckNvZGUpe0ZTLnN5bmNGU1JlcXVlc3RzLS07cmV0dXJuIGNhbGxiYWNrKGVyckNvZGUpfWZ1bmN0aW9uIGRvbmUoZXJyQ29kZSl7aWYoZXJyQ29kZSl7aWYoIWRvbmUuZXJyb3JlZCl7ZG9uZS5lcnJvcmVkPXRydWU7cmV0dXJuIGRvQ2FsbGJhY2soZXJyQ29kZSl9cmV0dXJufWlmKCsrY29tcGxldGVkPj1tb3VudHMubGVuZ3RoKXtkb0NhbGxiYWNrKG51bGwpfX1mb3IodmFyIG1vdW50IG9mIG1vdW50cyl7aWYobW91bnQudHlwZS5zeW5jZnMpe21vdW50LnR5cGUuc3luY2ZzKG1vdW50LHBvcHVsYXRlLGRvbmUpfWVsc2V7ZG9uZShudWxsKX19fSxtb3VudCh0eXBlLG9wdHMsbW91bnRwb2ludCl7dmFyIHJvb3Q9bW91bnRwb2ludD09PSIvIjt2YXIgcHNldWRvPSFtb3VudHBvaW50O3ZhciBub2RlO2lmKHJvb3QmJkZTLnJvb3Qpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDEwKX1lbHNlIGlmKCFyb290JiYhcHNldWRvKXt2YXIgbG9va3VwPUZTLmxvb2t1cFBhdGgobW91bnRwb2ludCx7Zm9sbG93X21vdW50OmZhbHNlfSk7bW91bnRwb2ludD1sb29rdXAucGF0aDtub2RlPWxvb2t1cC5ub2RlO2lmKEZTLmlzTW91bnRwb2ludChub2RlKSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoMTApfWlmKCFGUy5pc0Rpcihub2RlLm1vZGUpKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig1NCl9fXZhciBtb3VudD17dHlwZSxvcHRzLG1vdW50cG9pbnQsbW91bnRzOltdfTt2YXIgbW91bnRSb290PXR5cGUubW91bnQobW91bnQpO21vdW50Um9vdC5tb3VudD1tb3VudDttb3VudC5yb290PW1vdW50Um9vdDtpZihyb290KXtGUy5yb290PW1vdW50Um9vdH1lbHNlIGlmKG5vZGUpe25vZGUubW91bnRlZD1tb3VudDtpZihub2RlLm1vdW50KXtub2RlLm1vdW50Lm1vdW50cy5wdXNoKG1vdW50KX19cmV0dXJuIG1vdW50Um9vdH0sdW5tb3VudChtb3VudHBvaW50KXt2YXIgbG9va3VwPUZTLmxvb2t1cFBhdGgobW91bnRwb2ludCx7Zm9sbG93X21vdW50OmZhbHNlfSk7aWYoIUZTLmlzTW91bnRwb2ludChsb29rdXAubm9kZSkpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX12YXIgbm9kZT1sb29rdXAubm9kZTt2YXIgbW91bnQ9bm9kZS5tb3VudGVkO3ZhciBtb3VudHM9RlMuZ2V0TW91bnRzKG1vdW50KTtmb3IodmFyW2hhc2gsY3VycmVudF1vZiBPYmplY3QuZW50cmllcyhGUy5uYW1lVGFibGUpKXt3aGlsZShjdXJyZW50KXt2YXIgbmV4dD1jdXJyZW50Lm5hbWVfbmV4dDtpZihtb3VudHMuaW5jbHVkZXMoY3VycmVudC5tb3VudCkpe0ZTLmRlc3Ryb3lOb2RlKGN1cnJlbnQpfWN1cnJlbnQ9bmV4dH19bm9kZS5tb3VudGVkPW51bGw7dmFyIGlkeD1ub2RlLm1vdW50Lm1vdW50cy5pbmRleE9mKG1vdW50KTtub2RlLm1vdW50Lm1vdW50cy5zcGxpY2UoaWR4LDEpfSxsb29rdXAocGFyZW50LG5hbWUpe3JldHVybiBwYXJlbnQubm9kZV9vcHMubG9va3VwKHBhcmVudCxuYW1lKX0sbWtub2QocGF0aCxtb2RlLGRldil7dmFyIGxvb2t1cD1GUy5sb29rdXBQYXRoKHBhdGgse3BhcmVudDp0cnVlfSk7dmFyIHBhcmVudD1sb29rdXAubm9kZTt2YXIgbmFtZT1QQVRILmJhc2VuYW1lKHBhdGgpO2lmKCFuYW1lKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyOCl9aWYobmFtZT09PSIuInx8bmFtZT09PSIuLiIpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDIwKX12YXIgZXJyQ29kZT1GUy5tYXlDcmVhdGUocGFyZW50LG5hbWUpO2lmKGVyckNvZGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKGVyckNvZGUpfWlmKCFwYXJlbnQubm9kZV9vcHMubWtub2Qpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDYzKX1yZXR1cm4gcGFyZW50Lm5vZGVfb3BzLm1rbm9kKHBhcmVudCxuYW1lLG1vZGUsZGV2KX0sc3RhdGZzKHBhdGgpe3JldHVybiBGUy5zdGF0ZnNOb2RlKEZTLmxvb2t1cFBhdGgocGF0aCx7Zm9sbG93OnRydWV9KS5ub2RlKX0sc3RhdGZzU3RyZWFtKHN0cmVhbSl7cmV0dXJuIEZTLnN0YXRmc05vZGUoc3RyZWFtLm5vZGUpfSxzdGF0ZnNOb2RlKG5vZGUpe3ZhciBydG49e2JzaXplOjQwOTYsZnJzaXplOjQwOTYsYmxvY2tzOjFlNixiZnJlZTo1ZTUsYmF2YWlsOjVlNSxmaWxlczpGUy5uZXh0SW5vZGUsZmZyZWU6RlMubmV4dElub2RlLTEsZnNpZDo0MixmbGFnczoyLG5hbWVsZW46MjU1fTtpZihub2RlLm5vZGVfb3BzLnN0YXRmcyl7T2JqZWN0LmFzc2lnbihydG4sbm9kZS5ub2RlX29wcy5zdGF0ZnMobm9kZS5tb3VudC5vcHRzLnJvb3QpKX1yZXR1cm4gcnRufSxjcmVhdGUocGF0aCxtb2RlPTQzOCl7bW9kZSY9NDA5NTttb2RlfD0zMjc2ODtyZXR1cm4gRlMubWtub2QocGF0aCxtb2RlLDApfSxta2RpcihwYXRoLG1vZGU9NTExKXttb2RlJj01MTF8NTEyO21vZGV8PTE2Mzg0O3JldHVybiBGUy5ta25vZChwYXRoLG1vZGUsMCl9LG1rZGlyVHJlZShwYXRoLG1vZGUpe3ZhciBkaXJzPXBhdGguc3BsaXQoIi8iKTt2YXIgZD0iIjtmb3IodmFyIGRpciBvZiBkaXJzKXtpZighZGlyKWNvbnRpbnVlO2lmKGR8fFBBVEguaXNBYnMocGF0aCkpZCs9Ii8iO2QrPWRpcjt0cnl7RlMubWtkaXIoZCxtb2RlKX1jYXRjaChlKXtpZihlLmVycm5vIT0yMCl0aHJvdyBlfX19LG1rZGV2KHBhdGgsbW9kZSxkZXYpe2lmKHR5cGVvZiBkZXY9PSJ1bmRlZmluZWQiKXtkZXY9bW9kZTttb2RlPTQzOH1tb2RlfD04MTkyO3JldHVybiBGUy5ta25vZChwYXRoLG1vZGUsZGV2KX0sc3ltbGluayhvbGRwYXRoLG5ld3BhdGgpe2lmKCFQQVRIX0ZTLnJlc29sdmUob2xkcGF0aCkpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDQ0KX12YXIgbG9va3VwPUZTLmxvb2t1cFBhdGgobmV3cGF0aCx7cGFyZW50OnRydWV9KTt2YXIgcGFyZW50PWxvb2t1cC5ub2RlO2lmKCFwYXJlbnQpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDQ0KX12YXIgbmV3bmFtZT1QQVRILmJhc2VuYW1lKG5ld3BhdGgpO3ZhciBlcnJDb2RlPUZTLm1heUNyZWF0ZShwYXJlbnQsbmV3bmFtZSk7aWYoZXJyQ29kZSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoZXJyQ29kZSl9aWYoIXBhcmVudC5ub2RlX29wcy5zeW1saW5rKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig2Myl9cmV0dXJuIHBhcmVudC5ub2RlX29wcy5zeW1saW5rKHBhcmVudCxuZXduYW1lLG9sZHBhdGgpfSxsaW5rKG9sZHBhdGgsbmV3cGF0aCxmbGFncyl7dmFyIGxvb2t1cD1GUy5sb29rdXBQYXRoKG5ld3BhdGgse3BhcmVudDp0cnVlfSk7dmFyIHBhcmVudD1sb29rdXAubm9kZTtpZighcGFyZW50KXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig0NCl9dmFyIG5ld25hbWU9UEFUSC5iYXNlbmFtZShuZXdwYXRoKTt2YXIgZXJyQ29kZT1GUy5tYXlDcmVhdGUocGFyZW50LG5ld25hbWUpO2lmKGVyckNvZGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKGVyckNvZGUpfWlmKCFwYXJlbnQubm9kZV9vcHMubGluayl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoMzQpfXJldHVybiBwYXJlbnQubm9kZV9vcHMubGluayhwYXJlbnQsbmV3bmFtZSxvbGRwYXRoLGZsYWdzKX0scmVuYW1lKG9sZF9wYXRoLG5ld19wYXRoKXt2YXIgb2xkX2Rpcm5hbWU9UEFUSC5kaXJuYW1lKG9sZF9wYXRoKTt2YXIgbmV3X2Rpcm5hbWU9UEFUSC5kaXJuYW1lKG5ld19wYXRoKTt2YXIgb2xkX25hbWU9UEFUSC5iYXNlbmFtZShvbGRfcGF0aCk7dmFyIG5ld19uYW1lPVBBVEguYmFzZW5hbWUobmV3X3BhdGgpO3ZhciBsb29rdXAsb2xkX2RpcixuZXdfZGlyO2xvb2t1cD1GUy5sb29rdXBQYXRoKG9sZF9wYXRoLHtwYXJlbnQ6dHJ1ZX0pO29sZF9kaXI9bG9va3VwLm5vZGU7bG9va3VwPUZTLmxvb2t1cFBhdGgobmV3X3BhdGgse3BhcmVudDp0cnVlfSk7bmV3X2Rpcj1sb29rdXAubm9kZTtpZighb2xkX2Rpcnx8IW5ld19kaXIpdGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNDQpO2lmKG9sZF9kaXIubW91bnQhPT1uZXdfZGlyLm1vdW50KXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig3NSl9dmFyIG9sZF9ub2RlPUZTLmxvb2t1cE5vZGUob2xkX2RpcixvbGRfbmFtZSk7dmFyIHJlbGF0aXZlPVBBVEhfRlMucmVsYXRpdmUob2xkX3BhdGgsbmV3X2Rpcm5hbWUpO2lmKHJlbGF0aXZlLmNoYXJBdCgwKSE9PSIuIil7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoMjgpfXJlbGF0aXZlPVBBVEhfRlMucmVsYXRpdmUobmV3X3BhdGgsb2xkX2Rpcm5hbWUpO2lmKHJlbGF0aXZlLmNoYXJBdCgwKSE9PSIuIil7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNTUpfXZhciBuZXdfbm9kZTt0cnl7bmV3X25vZGU9RlMubG9va3VwTm9kZShuZXdfZGlyLG5ld19uYW1lKX1jYXRjaChlKXt9aWYob2xkX25vZGU9PT1uZXdfbm9kZSl7cmV0dXJufXZhciBpc2Rpcj1GUy5pc0RpcihvbGRfbm9kZS5tb2RlKTt2YXIgZXJyQ29kZT1GUy5tYXlEZWxldGUob2xkX2RpcixvbGRfbmFtZSxpc2Rpcik7aWYoZXJyQ29kZSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoZXJyQ29kZSl9ZXJyQ29kZT1uZXdfbm9kZT9GUy5tYXlEZWxldGUobmV3X2RpcixuZXdfbmFtZSxpc2Rpcik6RlMubWF5Q3JlYXRlKG5ld19kaXIsbmV3X25hbWUpO2lmKGVyckNvZGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKGVyckNvZGUpfWlmKCFvbGRfZGlyLm5vZGVfb3BzLnJlbmFtZSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNjMpfWlmKEZTLmlzTW91bnRwb2ludChvbGRfbm9kZSl8fG5ld19ub2RlJiZGUy5pc01vdW50cG9pbnQobmV3X25vZGUpKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigxMCl9aWYobmV3X2RpciE9PW9sZF9kaXIpe2VyckNvZGU9RlMubm9kZVBlcm1pc3Npb25zKG9sZF9kaXIsInciKTtpZihlcnJDb2RlKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcihlcnJDb2RlKX19RlMuaGFzaFJlbW92ZU5vZGUob2xkX25vZGUpO3RyeXtvbGRfZGlyLm5vZGVfb3BzLnJlbmFtZShvbGRfbm9kZSxuZXdfZGlyLG5ld19uYW1lKTtvbGRfbm9kZS5wYXJlbnQ9bmV3X2Rpcn1jYXRjaChlKXt0aHJvdyBlfWZpbmFsbHl7RlMuaGFzaEFkZE5vZGUob2xkX25vZGUpfX0scm1kaXIocGF0aCl7dmFyIGxvb2t1cD1GUy5sb29rdXBQYXRoKHBhdGgse3BhcmVudDp0cnVlfSk7dmFyIHBhcmVudD1sb29rdXAubm9kZTt2YXIgbmFtZT1QQVRILmJhc2VuYW1lKHBhdGgpO3ZhciBub2RlPUZTLmxvb2t1cE5vZGUocGFyZW50LG5hbWUpO3ZhciBlcnJDb2RlPUZTLm1heURlbGV0ZShwYXJlbnQsbmFtZSx0cnVlKTtpZihlcnJDb2RlKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcihlcnJDb2RlKX1pZighcGFyZW50Lm5vZGVfb3BzLnJtZGlyKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig2Myl9aWYoRlMuaXNNb3VudHBvaW50KG5vZGUpKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigxMCl9cGFyZW50Lm5vZGVfb3BzLnJtZGlyKHBhcmVudCxuYW1lKTtGUy5kZXN0cm95Tm9kZShub2RlKX0scmVhZGRpcihwYXRoKXt2YXIgbG9va3VwPUZTLmxvb2t1cFBhdGgocGF0aCx7Zm9sbG93OnRydWV9KTt2YXIgbm9kZT1sb29rdXAubm9kZTt2YXIgcmVhZGRpcj1GUy5jaGVja09wRXhpc3RzKG5vZGUubm9kZV9vcHMucmVhZGRpciw1NCk7cmV0dXJuIHJlYWRkaXIobm9kZSl9LHVubGluayhwYXRoKXt2YXIgbG9va3VwPUZTLmxvb2t1cFBhdGgocGF0aCx7cGFyZW50OnRydWV9KTt2YXIgcGFyZW50PWxvb2t1cC5ub2RlO2lmKCFwYXJlbnQpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDQ0KX12YXIgbmFtZT1QQVRILmJhc2VuYW1lKHBhdGgpO3ZhciBub2RlPUZTLmxvb2t1cE5vZGUocGFyZW50LG5hbWUpO3ZhciBlcnJDb2RlPUZTLm1heURlbGV0ZShwYXJlbnQsbmFtZSxmYWxzZSk7aWYoZXJyQ29kZSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoZXJyQ29kZSl9aWYoIXBhcmVudC5ub2RlX29wcy51bmxpbmspe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDYzKX1pZihGUy5pc01vdW50cG9pbnQobm9kZSkpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDEwKX1wYXJlbnQubm9kZV9vcHMudW5saW5rKHBhcmVudCxuYW1lKTtGUy5kZXN0cm95Tm9kZShub2RlKX0scmVhZGxpbmsocGF0aCl7dmFyIGxvb2t1cD1GUy5sb29rdXBQYXRoKHBhdGgpO3ZhciBsaW5rPWxvb2t1cC5ub2RlO2lmKCFsaW5rKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig0NCl9aWYoIWxpbmsubm9kZV9vcHMucmVhZGxpbmspe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX1yZXR1cm4gbGluay5ub2RlX29wcy5yZWFkbGluayhsaW5rKX0sc3RhdChwYXRoLGRvbnRGb2xsb3cpe3ZhciBsb29rdXA9RlMubG9va3VwUGF0aChwYXRoLHtmb2xsb3c6IWRvbnRGb2xsb3d9KTt2YXIgbm9kZT1sb29rdXAubm9kZTt2YXIgZ2V0YXR0cj1GUy5jaGVja09wRXhpc3RzKG5vZGUubm9kZV9vcHMuZ2V0YXR0ciw2Myk7cmV0dXJuIGdldGF0dHIobm9kZSl9LGZzdGF0KGZkKXt2YXIgc3RyZWFtPUZTLmdldFN0cmVhbUNoZWNrZWQoZmQpO3ZhciBub2RlPXN0cmVhbS5ub2RlO3ZhciBnZXRhdHRyPXN0cmVhbS5zdHJlYW1fb3BzLmdldGF0dHI7dmFyIGFyZz1nZXRhdHRyP3N0cmVhbTpub2RlO2dldGF0dHI/Pz1ub2RlLm5vZGVfb3BzLmdldGF0dHI7RlMuY2hlY2tPcEV4aXN0cyhnZXRhdHRyLDYzKTtyZXR1cm4gZ2V0YXR0cihhcmcpfSxsc3RhdChwYXRoKXtyZXR1cm4gRlMuc3RhdChwYXRoLHRydWUpfSxkb0NobW9kKHN0cmVhbSxub2RlLG1vZGUsZG9udEZvbGxvdyl7RlMuZG9TZXRBdHRyKHN0cmVhbSxub2RlLHttb2RlOm1vZGUmNDA5NXxub2RlLm1vZGUmfjQwOTUsY3RpbWU6RGF0ZS5ub3coKSxkb250Rm9sbG93fSl9LGNobW9kKHBhdGgsbW9kZSxkb250Rm9sbG93KXt2YXIgbm9kZTtpZih0eXBlb2YgcGF0aD09InN0cmluZyIpe3ZhciBsb29rdXA9RlMubG9va3VwUGF0aChwYXRoLHtmb2xsb3c6IWRvbnRGb2xsb3d9KTtub2RlPWxvb2t1cC5ub2RlfWVsc2V7bm9kZT1wYXRofUZTLmRvQ2htb2QobnVsbCxub2RlLG1vZGUsZG9udEZvbGxvdyl9LGxjaG1vZChwYXRoLG1vZGUpe0ZTLmNobW9kKHBhdGgsbW9kZSx0cnVlKX0sZmNobW9kKGZkLG1vZGUpe3ZhciBzdHJlYW09RlMuZ2V0U3RyZWFtQ2hlY2tlZChmZCk7RlMuZG9DaG1vZChzdHJlYW0sc3RyZWFtLm5vZGUsbW9kZSxmYWxzZSl9LGRvQ2hvd24oc3RyZWFtLG5vZGUsZG9udEZvbGxvdyl7RlMuZG9TZXRBdHRyKHN0cmVhbSxub2RlLHt0aW1lc3RhbXA6RGF0ZS5ub3coKSxkb250Rm9sbG93fSl9LGNob3duKHBhdGgsdWlkLGdpZCxkb250Rm9sbG93KXt2YXIgbm9kZTtpZih0eXBlb2YgcGF0aD09InN0cmluZyIpe3ZhciBsb29rdXA9RlMubG9va3VwUGF0aChwYXRoLHtmb2xsb3c6IWRvbnRGb2xsb3d9KTtub2RlPWxvb2t1cC5ub2RlfWVsc2V7bm9kZT1wYXRofUZTLmRvQ2hvd24obnVsbCxub2RlLGRvbnRGb2xsb3cpfSxsY2hvd24ocGF0aCx1aWQsZ2lkKXtGUy5jaG93bihwYXRoLHVpZCxnaWQsdHJ1ZSl9LGZjaG93bihmZCx1aWQsZ2lkKXt2YXIgc3RyZWFtPUZTLmdldFN0cmVhbUNoZWNrZWQoZmQpO0ZTLmRvQ2hvd24oc3RyZWFtLHN0cmVhbS5ub2RlLGZhbHNlKX0sZG9UcnVuY2F0ZShzdHJlYW0sbm9kZSxsZW4pe2lmKEZTLmlzRGlyKG5vZGUubW9kZSkpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDMxKX1pZighRlMuaXNGaWxlKG5vZGUubW9kZSkpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX12YXIgZXJyQ29kZT1GUy5ub2RlUGVybWlzc2lvbnMobm9kZSwidyIpO2lmKGVyckNvZGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKGVyckNvZGUpfUZTLmRvU2V0QXR0cihzdHJlYW0sbm9kZSx7c2l6ZTpsZW4sdGltZXN0YW1wOkRhdGUubm93KCl9KX0sdHJ1bmNhdGUocGF0aCxsZW4pe2lmKGxlbjwwKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyOCl9dmFyIG5vZGU7aWYodHlwZW9mIHBhdGg9PSJzdHJpbmciKXt2YXIgbG9va3VwPUZTLmxvb2t1cFBhdGgocGF0aCx7Zm9sbG93OnRydWV9KTtub2RlPWxvb2t1cC5ub2RlfWVsc2V7bm9kZT1wYXRofUZTLmRvVHJ1bmNhdGUobnVsbCxub2RlLGxlbil9LGZ0cnVuY2F0ZShmZCxsZW4pe3ZhciBzdHJlYW09RlMuZ2V0U3RyZWFtQ2hlY2tlZChmZCk7aWYobGVuPDB8fChzdHJlYW0uZmxhZ3MmMjA5NzE1NSk9PT0wKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyOCl9RlMuZG9UcnVuY2F0ZShzdHJlYW0sc3RyZWFtLm5vZGUsbGVuKX0sdXRpbWUocGF0aCxhdGltZSxtdGltZSxkb250Rm9sbG93KXt2YXIgbG9va3VwPUZTLmxvb2t1cFBhdGgocGF0aCx7Zm9sbG93OiFkb250Rm9sbG93fSk7RlMuZG9TZXRBdHRyKG51bGwsbG9va3VwLm5vZGUse2F0aW1lLG10aW1lLGRvbnRGb2xsb3d9KX0sb3BlbihwYXRoLGZsYWdzLG1vZGU9NDM4KXtpZihwYXRoPT09IiIpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDQ0KX1mbGFncz1GU19tb2RlU3RyaW5nVG9GbGFncyhmbGFncyk7aWYoZmxhZ3MmNjQpe21vZGU9bW9kZSY0MDk1fDMyNzY4fWVsc2V7bW9kZT0wfXZhciBub2RlO3ZhciBpc0RpclBhdGg7aWYodHlwZW9mIHBhdGg9PSJvYmplY3QiKXtub2RlPXBhdGh9ZWxzZXtpc0RpclBhdGg9cGF0aC5lbmRzV2l0aCgiLyIpO3ZhciBsb29rdXA9RlMubG9va3VwUGF0aChwYXRoLHtmb2xsb3c6IShmbGFncyYxMzEwNzIpLG5vZW50X29rYXk6dHJ1ZX0pO25vZGU9bG9va3VwLm5vZGU7cGF0aD1sb29rdXAucGF0aH12YXIgY3JlYXRlZD1mYWxzZTtpZihmbGFncyY2NCl7aWYobm9kZSl7aWYoZmxhZ3MmMTI4KXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyMCl9fWVsc2UgaWYoaXNEaXJQYXRoKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigzMSl9ZWxzZXtub2RlPUZTLm1rbm9kKHBhdGgsbW9kZXw1MTEsMCk7Y3JlYXRlZD10cnVlfX1pZighbm9kZSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNDQpfWlmKEZTLmlzQ2hyZGV2KG5vZGUubW9kZSkpe2ZsYWdzJj1+NTEyfWlmKGZsYWdzJjY1NTM2JiYhRlMuaXNEaXIobm9kZS5tb2RlKSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNTQpfWlmKCFjcmVhdGVkKXt2YXIgZXJyQ29kZT1GUy5tYXlPcGVuKG5vZGUsZmxhZ3MpO2lmKGVyckNvZGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKGVyckNvZGUpfX1pZihmbGFncyY1MTImJiFjcmVhdGVkKXtGUy50cnVuY2F0ZShub2RlLDApfWZsYWdzJj1+KDEyOHw1MTJ8MTMxMDcyKTt2YXIgc3RyZWFtPUZTLmNyZWF0ZVN0cmVhbSh7bm9kZSxwYXRoOkZTLmdldFBhdGgobm9kZSksZmxhZ3Msc2Vla2FibGU6dHJ1ZSxwb3NpdGlvbjowLHN0cmVhbV9vcHM6bm9kZS5zdHJlYW1fb3BzLHVuZ290dGVuOltdLGVycm9yOmZhbHNlfSk7aWYoc3RyZWFtLnN0cmVhbV9vcHMub3Blbil7c3RyZWFtLnN0cmVhbV9vcHMub3BlbihzdHJlYW0pfWlmKGNyZWF0ZWQpe0ZTLmNobW9kKG5vZGUsbW9kZSY1MTEpfXJldHVybiBzdHJlYW19LGNsb3NlKHN0cmVhbSl7aWYoRlMuaXNDbG9zZWQoc3RyZWFtKSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoOCl9aWYoc3RyZWFtLmdldGRlbnRzKXN0cmVhbS5nZXRkZW50cz1udWxsO3N0cmVhbS5ub2RlPy5ub3RpZnlMaXN0ZW5lcnMoMzIpO3RyeXtpZihzdHJlYW0uc3RyZWFtX29wcy5jbG9zZSl7c3RyZWFtLnN0cmVhbV9vcHMuY2xvc2Uoc3RyZWFtKX19Y2F0Y2goZSl7dGhyb3cgZX1maW5hbGx5e0ZTLmNsb3NlU3RyZWFtKHN0cmVhbS5mZCl9c3RyZWFtLmZkPW51bGx9LGlzQ2xvc2VkKHN0cmVhbSl7cmV0dXJuIHN0cmVhbS5mZD09PW51bGx9LGxsc2VlayhzdHJlYW0sb2Zmc2V0LHdoZW5jZSl7aWYoRlMuaXNDbG9zZWQoc3RyZWFtKSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoOCl9aWYoIXN0cmVhbS5zZWVrYWJsZXx8IXN0cmVhbS5zdHJlYW1fb3BzLmxsc2Vlayl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNzApfWlmKHdoZW5jZSE9MCYmd2hlbmNlIT0xJiZ3aGVuY2UhPTIpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX1zdHJlYW0ucG9zaXRpb249c3RyZWFtLnN0cmVhbV9vcHMubGxzZWVrKHN0cmVhbSxvZmZzZXQsd2hlbmNlKTtzdHJlYW0udW5nb3R0ZW49W107cmV0dXJuIHN0cmVhbS5wb3NpdGlvbn0scmVhZChzdHJlYW0sYnVmZmVyLG9mZnNldCxsZW5ndGgscG9zaXRpb24pe2lmKGxlbmd0aDwwfHxwb3NpdGlvbjwwKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyOCl9aWYoRlMuaXNDbG9zZWQoc3RyZWFtKSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoOCl9aWYoKHN0cmVhbS5mbGFncyYyMDk3MTU1KT09PTEpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDgpfWlmKEZTLmlzRGlyKHN0cmVhbS5ub2RlLm1vZGUpKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigzMSl9aWYoIXN0cmVhbS5zdHJlYW1fb3BzLnJlYWQpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX12YXIgc2Vla2luZz10eXBlb2YgcG9zaXRpb24hPSJ1bmRlZmluZWQiO2lmKCFzZWVraW5nKXtwb3NpdGlvbj1zdHJlYW0ucG9zaXRpb259ZWxzZSBpZighc3RyZWFtLnNlZWthYmxlKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig3MCl9dmFyIGJ5dGVzUmVhZD1zdHJlYW0uc3RyZWFtX29wcy5yZWFkKHN0cmVhbSxidWZmZXIsb2Zmc2V0LGxlbmd0aCxwb3NpdGlvbik7aWYoIXNlZWtpbmcpc3RyZWFtLnBvc2l0aW9uKz1ieXRlc1JlYWQ7cmV0dXJuIGJ5dGVzUmVhZH0sd3JpdGUoc3RyZWFtLGJ1ZmZlcixvZmZzZXQsbGVuZ3RoLHBvc2l0aW9uLGNhbk93bil7aWYobGVuZ3RoPDB8fHBvc2l0aW9uPDApe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX1pZihGUy5pc0Nsb3NlZChzdHJlYW0pKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig4KX1pZigoc3RyZWFtLmZsYWdzJjIwOTcxNTUpPT09MCl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoOCl9aWYoRlMuaXNEaXIoc3RyZWFtLm5vZGUubW9kZSkpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDMxKX1pZighc3RyZWFtLnN0cmVhbV9vcHMud3JpdGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX1pZihzdHJlYW0uc2Vla2FibGUmJnN0cmVhbS5mbGFncyYxMDI0KXtGUy5sbHNlZWsoc3RyZWFtLDAsMil9dmFyIHNlZWtpbmc9dHlwZW9mIHBvc2l0aW9uIT0idW5kZWZpbmVkIjtpZighc2Vla2luZyl7cG9zaXRpb249c3RyZWFtLnBvc2l0aW9ufWVsc2UgaWYoIXN0cmVhbS5zZWVrYWJsZSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNzApfXZhciBieXRlc1dyaXR0ZW49c3RyZWFtLnN0cmVhbV9vcHMud3JpdGUoc3RyZWFtLGJ1ZmZlcixvZmZzZXQsbGVuZ3RoLHBvc2l0aW9uLGNhbk93bik7aWYoIXNlZWtpbmcpc3RyZWFtLnBvc2l0aW9uKz1ieXRlc1dyaXR0ZW47cmV0dXJuIGJ5dGVzV3JpdHRlbn0sbW1hcChzdHJlYW0sbGVuZ3RoLHBvc2l0aW9uLHByb3QsZmxhZ3Mpe2lmKHByb3QmMiYmIShmbGFncyYyKSYmKHN0cmVhbS5mbGFncyYyMDk3MTU1KSE9PTIpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDIpfWlmKChzdHJlYW0uZmxhZ3MmMjA5NzE1NSk9PT0xKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyKX1pZighc3RyZWFtLnN0cmVhbV9vcHMubW1hcCl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNDMpfWlmKCFsZW5ndGgpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKDI4KX1yZXR1cm4gc3RyZWFtLnN0cmVhbV9vcHMubW1hcChzdHJlYW0sbGVuZ3RoLHBvc2l0aW9uLHByb3QsZmxhZ3MpfSxtc3luYyhzdHJlYW0sYnVmZmVyLG9mZnNldCxsZW5ndGgsbW1hcEZsYWdzKXtpZighc3RyZWFtLnN0cmVhbV9vcHMubXN5bmMpe3JldHVybiAwfXJldHVybiBzdHJlYW0uc3RyZWFtX29wcy5tc3luYyhzdHJlYW0sYnVmZmVyLG9mZnNldCxsZW5ndGgsbW1hcEZsYWdzKX0saW9jdGwoc3RyZWFtLGNtZCxhcmcpe2lmKCFzdHJlYW0uc3RyZWFtX29wcy5pb2N0bCl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNTkpfXJldHVybiBzdHJlYW0uc3RyZWFtX29wcy5pb2N0bChzdHJlYW0sY21kLGFyZyl9LHJlYWRGaWxlKHBhdGgsb3B0cz17fSl7b3B0cy5mbGFncz1vcHRzLmZsYWdzPz8wO29wdHMuZW5jb2Rpbmc9b3B0cy5lbmNvZGluZz8/ImJpbmFyeSI7aWYob3B0cy5lbmNvZGluZyE9PSJ1dGY4IiYmb3B0cy5lbmNvZGluZyE9PSJiaW5hcnkiKXthYm9ydChgSW52YWxpZCBlbmNvZGluZyB0eXBlICIke29wdHMuZW5jb2Rpbmd9ImApfXZhciBzdHJlYW09RlMub3BlbihwYXRoLG9wdHMuZmxhZ3MpO3ZhciBzdGF0PUZTLnN0YXQocGF0aCk7dmFyIGxlbmd0aD1zdGF0LnNpemU7dmFyIGJ1Zj1uZXcgVWludDhBcnJheShsZW5ndGgpO0ZTLnJlYWQoc3RyZWFtLGJ1ZiwwLGxlbmd0aCwwKTtpZihvcHRzLmVuY29kaW5nPT09InV0ZjgiKXtidWY9VVRGOEFycmF5VG9TdHJpbmcoYnVmKX1GUy5jbG9zZShzdHJlYW0pO3JldHVybiBidWZ9LHdyaXRlRmlsZShwYXRoLGRhdGEsb3B0cz17fSl7b3B0cy5mbGFncz1vcHRzLmZsYWdzPz81Nzc7dmFyIHN0cmVhbT1GUy5vcGVuKHBhdGgsb3B0cy5mbGFncyxvcHRzLm1vZGUpO2RhdGE9RlNfZmlsZURhdGFUb1R5cGVkQXJyYXkoZGF0YSk7RlMud3JpdGUoc3RyZWFtLGRhdGEsMCxkYXRhLmJ5dGVMZW5ndGgsdW5kZWZpbmVkLG9wdHMuY2FuT3duKTtGUy5jbG9zZShzdHJlYW0pfSxjd2Q6KCk9PkZTLmN1cnJlbnRQYXRoLGNoZGlyKHBhdGgpe3ZhciBsb29rdXA9RlMubG9va3VwUGF0aChwYXRoLHtmb2xsb3c6dHJ1ZX0pO2lmKGxvb2t1cC5ub2RlPT09bnVsbCl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNDQpfWlmKCFGUy5pc0Rpcihsb29rdXAubm9kZS5tb2RlKSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoNTQpfXZhciBlcnJDb2RlPUZTLm5vZGVQZXJtaXNzaW9ucyhsb29rdXAubm9kZSwieCIpO2lmKGVyckNvZGUpe3Rocm93IG5ldyBGUy5FcnJub0Vycm9yKGVyckNvZGUpfUZTLmN1cnJlbnRQYXRoPWxvb2t1cC5wYXRofSxjcmVhdGVEZWZhdWx0RGlyZWN0b3JpZXMoKXtGUy5ta2RpcigiL3RtcCIpO0ZTLm1rZGlyKCIvaG9tZSIpO0ZTLm1rZGlyKCIvaG9tZS93ZWJfdXNlciIpfSxjcmVhdGVEZWZhdWx0RGV2aWNlcygpe0ZTLm1rZGlyKCIvZGV2Iik7RlMucmVnaXN0ZXJEZXZpY2UoRlMubWFrZWRldigxLDMpLHtyZWFkOigpPT4wLHdyaXRlOihzdHJlYW0sYnVmZmVyLG9mZnNldCxsZW5ndGgscG9zKT0+bGVuZ3RoLGxsc2VlazooKT0+MH0pO0ZTLm1rZGV2KCIvZGV2L251bGwiLEZTLm1ha2VkZXYoMSwzKSk7VFRZLnJlZ2lzdGVyKEZTLm1ha2VkZXYoNSwwKSxUVFkuZGVmYXVsdF90dHlfb3BzKTtUVFkucmVnaXN0ZXIoRlMubWFrZWRldig2LDApLFRUWS5kZWZhdWx0X3R0eTFfb3BzKTtGUy5ta2RldigiL2Rldi90dHkiLEZTLm1ha2VkZXYoNSwwKSk7RlMubWtkZXYoIi9kZXYvdHR5MSIsRlMubWFrZWRldig2LDApKTt2YXIgcmFuZG9tQnVmZmVyPW5ldyBVaW50OEFycmF5KDEwMjQpLHJhbmRvbUxlZnQ9MDt2YXIgcmFuZG9tQnl0ZT0oKT0+e2lmKCFyYW5kb21MZWZ0KXtyYW5kb21GaWxsKHJhbmRvbUJ1ZmZlcik7cmFuZG9tTGVmdD1yYW5kb21CdWZmZXIuYnl0ZUxlbmd0aH1yZXR1cm4gcmFuZG9tQnVmZmVyWy0tcmFuZG9tTGVmdF19O0ZTLmNyZWF0ZURldmljZSgiL2RldiIsInJhbmRvbSIscmFuZG9tQnl0ZSk7RlMuY3JlYXRlRGV2aWNlKCIvZGV2IiwidXJhbmRvbSIscmFuZG9tQnl0ZSk7RlMubWtkaXIoIi9kZXYvc2htIik7RlMubWtkaXIoIi9kZXYvc2htL3RtcCIpfSxjcmVhdGVTcGVjaWFsRGlyZWN0b3JpZXMoKXtGUy5ta2RpcigiL3Byb2MiKTt2YXIgcHJvY19zZWxmPUZTLm1rZGlyKCIvcHJvYy9zZWxmIik7RlMubWtkaXIoIi9wcm9jL3NlbGYvZmQiKTtGUy5tb3VudCh7bW91bnQoKXt2YXIgbm9kZT1GUy5jcmVhdGVOb2RlKHByb2Nfc2VsZiwiZmQiLDE2ODk1LDczKTtub2RlLnN0cmVhbV9vcHM9e2xsc2VlazpNRU1GUy5zdHJlYW1fb3BzLmxsc2Vla307bm9kZS5ub2RlX29wcz17bG9va3VwKHBhcmVudCxuYW1lKXt2YXIgZmQ9K25hbWU7dmFyIHN0cmVhbT1GUy5nZXRTdHJlYW1DaGVja2VkKGZkKTt2YXIgcmV0PXtwYXJlbnQ6bnVsbCxtb3VudDp7bW91bnRwb2ludDoiZmFrZSJ9LG5vZGVfb3BzOntyZWFkbGluazooKT0+c3RyZWFtLnBhdGh9LGlkOmZkKzF9O3JldC5wYXJlbnQ9cmV0O3JldHVybiByZXR9LHJlYWRkaXIoKXtyZXR1cm4gQXJyYXkuZnJvbShGUy5zdHJlYW1zLmVudHJpZXMoKSkuZmlsdGVyKChbayx2XSk9PnYpLm1hcCgoW2ssdl0pPT5rLnRvU3RyaW5nKCkpfX07cmV0dXJuIG5vZGV9fSx7fSwiL3Byb2Mvc2VsZi9mZCIpfSxjcmVhdGVTdGFuZGFyZFN0cmVhbXMoaW5wdXQsb3V0cHV0LGVycm9yKXtpZihpbnB1dCl7RlMuY3JlYXRlRGV2aWNlKCIvZGV2Iiwic3RkaW4iLGlucHV0KX1lbHNle0ZTLnN5bWxpbmsoIi9kZXYvdHR5IiwiL2Rldi9zdGRpbiIpfWlmKG91dHB1dCl7RlMuY3JlYXRlRGV2aWNlKCIvZGV2Iiwic3Rkb3V0IixudWxsLG91dHB1dCl9ZWxzZXtGUy5zeW1saW5rKCIvZGV2L3R0eSIsIi9kZXYvc3Rkb3V0Iil9aWYoZXJyb3Ipe0ZTLmNyZWF0ZURldmljZSgiL2RldiIsInN0ZGVyciIsbnVsbCxlcnJvcil9ZWxzZXtGUy5zeW1saW5rKCIvZGV2L3R0eTEiLCIvZGV2L3N0ZGVyciIpfXZhciBzdGRpbj1GUy5vcGVuKCIvZGV2L3N0ZGluIiwwKTt2YXIgc3Rkb3V0PUZTLm9wZW4oIi9kZXYvc3Rkb3V0IiwxKTt2YXIgc3RkZXJyPUZTLm9wZW4oIi9kZXYvc3RkZXJyIiwxKX0sc3RhdGljSW5pdCgpe0ZTLm5hbWVUYWJsZT1uZXcgQXJyYXkoNDA5Nik7RlMubW91bnQoTUVNRlMse30sIi8iKTtGUy5jcmVhdGVEZWZhdWx0RGlyZWN0b3JpZXMoKTtGUy5jcmVhdGVEZWZhdWx0RGV2aWNlcygpO0ZTLmNyZWF0ZVNwZWNpYWxEaXJlY3RvcmllcygpO0ZTLmZpbGVzeXN0ZW1zPXtNRU1GU319LGluaXQoaW5wdXQsb3V0cHV0LGVycm9yKXtGUy5pbml0aWFsaXplZD10cnVlO2lucHV0Pz89TW9kdWxlWyJzdGRpbiJdO291dHB1dD8/PU1vZHVsZVsic3Rkb3V0Il07ZXJyb3I/Pz1Nb2R1bGVbInN0ZGVyciJdO0ZTLmNyZWF0ZVN0YW5kYXJkU3RyZWFtcyhpbnB1dCxvdXRwdXQsZXJyb3IpfSxxdWl0KCl7RlMuaW5pdGlhbGl6ZWQ9ZmFsc2U7Zm9yKHZhciBzdHJlYW0gb2YgRlMuc3RyZWFtcyl7aWYoc3RyZWFtKXtGUy5jbG9zZShzdHJlYW0pfX19LGZpbmRPYmplY3QocGF0aCxkb250UmVzb2x2ZUxhc3RMaW5rKXt2YXIgcmV0PUZTLmFuYWx5emVQYXRoKHBhdGgsZG9udFJlc29sdmVMYXN0TGluayk7aWYoIXJldC5leGlzdHMpe3JldHVybiBudWxsfXJldHVybiByZXQub2JqZWN0fSxhbmFseXplUGF0aChwYXRoLGRvbnRSZXNvbHZlTGFzdExpbmspe3RyeXt2YXIgbG9va3VwPUZTLmxvb2t1cFBhdGgocGF0aCx7Zm9sbG93OiFkb250UmVzb2x2ZUxhc3RMaW5rfSk7cGF0aD1sb29rdXAucGF0aH1jYXRjaChlKXt9dmFyIHJldD17aXNSb290OmZhbHNlLGV4aXN0czpmYWxzZSxlcnJvcjowLG5hbWU6bnVsbCxwYXRoOm51bGwsb2JqZWN0Om51bGwscGFyZW50RXhpc3RzOmZhbHNlLHBhcmVudFBhdGg6bnVsbCxwYXJlbnRPYmplY3Q6bnVsbH07dHJ5e3ZhciBsb29rdXA9RlMubG9va3VwUGF0aChwYXRoLHtwYXJlbnQ6dHJ1ZX0pO3JldC5wYXJlbnRFeGlzdHM9dHJ1ZTtyZXQucGFyZW50UGF0aD1sb29rdXAucGF0aDtyZXQucGFyZW50T2JqZWN0PWxvb2t1cC5ub2RlO3JldC5uYW1lPVBBVEguYmFzZW5hbWUocGF0aCk7bG9va3VwPUZTLmxvb2t1cFBhdGgocGF0aCx7Zm9sbG93OiFkb250UmVzb2x2ZUxhc3RMaW5rfSk7cmV0LmV4aXN0cz10cnVlO3JldC5wYXRoPWxvb2t1cC5wYXRoO3JldC5vYmplY3Q9bG9va3VwLm5vZGU7cmV0Lm5hbWU9bG9va3VwLm5vZGUubmFtZTtyZXQuaXNSb290PWxvb2t1cC5wYXRoPT09Ii8ifWNhdGNoKGUpe3JldC5lcnJvcj1lLmVycm5vfXJldHVybiByZXR9LGNyZWF0ZVBhdGgocGFyZW50LHBhdGgsY2FuUmVhZCxjYW5Xcml0ZSl7cGFyZW50PXR5cGVvZiBwYXJlbnQ9PSJzdHJpbmciP3BhcmVudDpGUy5nZXRQYXRoKHBhcmVudCk7dmFyIHBhcnRzPXBhdGguc3BsaXQoIi8iKS5yZXZlcnNlKCk7d2hpbGUocGFydHMubGVuZ3RoKXt2YXIgcGFydD1wYXJ0cy5wb3AoKTtpZighcGFydCljb250aW51ZTt2YXIgY3VycmVudD1QQVRILmpvaW4yKHBhcmVudCxwYXJ0KTt0cnl7RlMubWtkaXIoY3VycmVudCl9Y2F0Y2goZSl7aWYoZS5lcnJubyE9MjApdGhyb3cgZX1wYXJlbnQ9Y3VycmVudH1yZXR1cm4gY3VycmVudH0sY3JlYXRlRmlsZShwYXJlbnQsbmFtZSxwcm9wZXJ0aWVzLGNhblJlYWQsY2FuV3JpdGUpe3ZhciBwYXRoPVBBVEguam9pbjIodHlwZW9mIHBhcmVudD09InN0cmluZyI/cGFyZW50OkZTLmdldFBhdGgocGFyZW50KSxuYW1lKTt2YXIgbW9kZT1GU19nZXRNb2RlKGNhblJlYWQsY2FuV3JpdGUpO3JldHVybiBGUy5jcmVhdGUocGF0aCxtb2RlKX0sY3JlYXRlRGF0YUZpbGUocGFyZW50LG5hbWUsZGF0YSxjYW5SZWFkLGNhbldyaXRlLGNhbk93bil7dmFyIHBhdGg9bmFtZTtpZihwYXJlbnQpe3BhcmVudD10eXBlb2YgcGFyZW50PT0ic3RyaW5nIj9wYXJlbnQ6RlMuZ2V0UGF0aChwYXJlbnQpO3BhdGg9bmFtZT9QQVRILmpvaW4yKHBhcmVudCxuYW1lKTpwYXJlbnR9dmFyIG1vZGU9RlNfZ2V0TW9kZShjYW5SZWFkLGNhbldyaXRlKTt2YXIgbm9kZT1GUy5jcmVhdGUocGF0aCxtb2RlKTtpZihkYXRhKXtkYXRhPUZTX2ZpbGVEYXRhVG9UeXBlZEFycmF5KGRhdGEpO0ZTLmNobW9kKG5vZGUsbW9kZXwxNDYpO3ZhciBzdHJlYW09RlMub3Blbihub2RlLDU3Nyk7RlMud3JpdGUoc3RyZWFtLGRhdGEsMCxkYXRhLmxlbmd0aCwwLGNhbk93bik7RlMuY2xvc2Uoc3RyZWFtKTtGUy5jaG1vZChub2RlLG1vZGUpfX0sY3JlYXRlRGV2aWNlKHBhcmVudCxuYW1lLGlucHV0LG91dHB1dCl7dmFyIHBhdGg9UEFUSC5qb2luMih0eXBlb2YgcGFyZW50PT0ic3RyaW5nIj9wYXJlbnQ6RlMuZ2V0UGF0aChwYXJlbnQpLG5hbWUpO3ZhciBtb2RlPUZTX2dldE1vZGUoISFpbnB1dCwhIW91dHB1dCk7RlMuY3JlYXRlRGV2aWNlLm1ham9yPz89NjQ7dmFyIGRldj1GUy5tYWtlZGV2KEZTLmNyZWF0ZURldmljZS5tYWpvcisrLDApO0ZTLnJlZ2lzdGVyRGV2aWNlKGRldix7b3BlbihzdHJlYW0pe3N0cmVhbS5zZWVrYWJsZT1mYWxzZX0sY2xvc2Uoc3RyZWFtKXtpZihvdXRwdXQ/LmJ1ZmZlcj8ubGVuZ3RoKXtvdXRwdXQoMTApfX0scmVhZChzdHJlYW0sYnVmZmVyLG9mZnNldCxsZW5ndGgscG9zKXt2YXIgYnl0ZXNSZWFkPTA7Zm9yKHZhciBpPTA7aTxsZW5ndGg7aSsrKXt2YXIgcmVzdWx0O3RyeXtyZXN1bHQ9aW5wdXQoKX1jYXRjaChlKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyOSl9aWYocmVzdWx0PT09dW5kZWZpbmVkJiYhYnl0ZXNSZWFkKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig2KX1pZihyZXN1bHQ9PT1udWxsfHxyZXN1bHQ9PT11bmRlZmluZWQpYnJlYWs7Ynl0ZXNSZWFkKys7YnVmZmVyW29mZnNldCtpXT1yZXN1bHR9aWYoYnl0ZXNSZWFkKXtzdHJlYW0ubm9kZS5hdGltZT1EYXRlLm5vdygpfXJldHVybiBieXRlc1JlYWR9LHdyaXRlKHN0cmVhbSxidWZmZXIsb2Zmc2V0LGxlbmd0aCxwb3Mpe2Zvcih2YXIgaT0wO2k8bGVuZ3RoO2krKyl7dHJ5e291dHB1dChidWZmZXJbb2Zmc2V0K2ldKX1jYXRjaChlKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcigyOSl9fWlmKGxlbmd0aCl7c3RyZWFtLm5vZGUubXRpbWU9c3RyZWFtLm5vZGUuY3RpbWU9RGF0ZS5ub3coKX1yZXR1cm4gaX19KTtyZXR1cm4gRlMubWtkZXYocGF0aCxtb2RlLGRldil9LGZvcmNlTG9hZEZpbGUob2JqKXtpZihvYmouaXNEZXZpY2V8fG9iai5pc0ZvbGRlcnx8b2JqLmxpbmt8fG9iai5jb250ZW50cylyZXR1cm4gdHJ1ZTtpZihnbG9iYWxUaGlzLlhNTEh0dHBSZXF1ZXN0KXthYm9ydCgiTGF6eSBsb2FkaW5nIHNob3VsZCBoYXZlIGJlZW4gcGVyZm9ybWVkIChjb250ZW50cyBzZXQpIGluIGNyZWF0ZUxhenlGaWxlLCBidXQgaXQgd2FzIG5vdC4gTGF6eSBsb2FkaW5nIG9ubHkgd29ya3MgaW4gd2ViIHdvcmtlcnMuIFVzZSAtLWVtYmVkLWZpbGUgb3IgLS1wcmVsb2FkLWZpbGUgaW4gZW1jYyBvbiB0aGUgbWFpbiB0aHJlYWQuIil9ZWxzZXt0cnl7b2JqLmNvbnRlbnRzPXJlYWRCaW5hcnkob2JqLnVybCl9Y2F0Y2goZSl7dGhyb3cgbmV3IEZTLkVycm5vRXJyb3IoMjkpfX19LGNyZWF0ZUxhenlGaWxlKHBhcmVudCxuYW1lLHVybCxjYW5SZWFkLGNhbldyaXRlKXtjbGFzcyBMYXp5VWludDhBcnJheXtsZW5ndGhLbm93bj1mYWxzZTtjaHVua3M9W107Z2V0KGlkeCl7aWYoaWR4PnRoaXMubGVuZ3RoLTF8fGlkeDwwKXtyZXR1cm4gdW5kZWZpbmVkfXZhciBjaHVua09mZnNldD1pZHgldGhpcy5jaHVua1NpemU7dmFyIGNodW5rTnVtPWlkeC90aGlzLmNodW5rU2l6ZXwwO3JldHVybiB0aGlzLmdldHRlcihjaHVua051bSlbY2h1bmtPZmZzZXRdfXNldERhdGFHZXR0ZXIoZ2V0dGVyKXt0aGlzLmdldHRlcj1nZXR0ZXJ9Y2FjaGVMZW5ndGgoKXt2YXIgeGhyPW5ldyBYTUxIdHRwUmVxdWVzdDt4aHIub3BlbigiSEVBRCIsdXJsLGZhbHNlKTt4aHIuc2VuZChudWxsKTtpZighKHhoci5zdGF0dXM+PTIwMCYmeGhyLnN0YXR1czwzMDB8fHhoci5zdGF0dXM9PT0zMDQpKWFib3J0KGBDb3VsZG4ndCBsb2FkICR7dXJsfS4gU3RhdHVzOiAke3hoci5zdGF0dXN9YCk7dmFyIGRhdGFsZW5ndGg9TnVtYmVyKHhoci5nZXRSZXNwb25zZUhlYWRlcigiQ29udGVudC1sZW5ndGgiKSk7dmFyIGhlYWRlcjt2YXIgaGFzQnl0ZVNlcnZpbmc9KGhlYWRlcj14aHIuZ2V0UmVzcG9uc2VIZWFkZXIoIkFjY2VwdC1SYW5nZXMiKSkmJmhlYWRlcj09PSJieXRlcyI7dmFyIHVzZXNHemlwPShoZWFkZXI9eGhyLmdldFJlc3BvbnNlSGVhZGVyKCJDb250ZW50LUVuY29kaW5nIikpJiZoZWFkZXI9PT0iZ3ppcCI7dmFyIGNodW5rU2l6ZT0xMDI0KjEwMjQ7aWYoIWhhc0J5dGVTZXJ2aW5nKWNodW5rU2l6ZT1kYXRhbGVuZ3RoO3ZhciBkb1hIUj0oZnJvbSx0byk9PntpZihmcm9tPnRvKWFib3J0KGBpbnZhbGlkIHJhbmdlICgke2Zyb219LCAke3RvfSkgb3Igbm8gYnl0ZXMgcmVxdWVzdGVkIWApO2lmKHRvPmRhdGFsZW5ndGgtMSlhYm9ydChgb25seSAke2RhdGFsZW5ndGh9IGJ5dGVzIGF2YWlsYWJsZSEgcHJvZ3JhbW1lciBlcnJvciFgKTt2YXIgeGhyPW5ldyBYTUxIdHRwUmVxdWVzdDt4aHIub3BlbigiR0VUIix1cmwsZmFsc2UpO2lmKGRhdGFsZW5ndGghPT1jaHVua1NpemUpeGhyLnNldFJlcXVlc3RIZWFkZXIoIlJhbmdlIixgYnl0ZXM9JHtmcm9tfS0ke3RvfWApO3hoci5yZXNwb25zZVR5cGU9ImFycmF5YnVmZmVyIjtpZih4aHIub3ZlcnJpZGVNaW1lVHlwZSl7eGhyLm92ZXJyaWRlTWltZVR5cGUoInRleHQvcGxhaW47IGNoYXJzZXQ9eC11c2VyLWRlZmluZWQiKX14aHIuc2VuZChudWxsKTtpZighKHhoci5zdGF0dXM+PTIwMCYmeGhyLnN0YXR1czwzMDB8fHhoci5zdGF0dXM9PT0zMDQpKWFib3J0KGBDb3VsZG4ndCBsb2FkICR7dXJsfS4gU3RhdHVzOiAke3hoci5zdGF0dXN9YCk7aWYoeGhyLnJlc3BvbnNlIT09dW5kZWZpbmVkKXtyZXR1cm4gbmV3IFVpbnQ4QXJyYXkoeGhyLnJlc3BvbnNlfHxbXSl9cmV0dXJuIGludEFycmF5RnJvbVN0cmluZyh4aHIucmVzcG9uc2VUZXh0Pz8iIix0cnVlKX07dmFyIGxhenlBcnJheT10aGlzO2xhenlBcnJheS5zZXREYXRhR2V0dGVyKGNodW5rTnVtPT57dmFyIHN0YXJ0PWNodW5rTnVtKmNodW5rU2l6ZTt2YXIgZW5kPShjaHVua051bSsxKSpjaHVua1NpemUtMTtlbmQ9TWF0aC5taW4oZW5kLGRhdGFsZW5ndGgtMSk7aWYodHlwZW9mIGxhenlBcnJheS5jaHVua3NbY2h1bmtOdW1dPT0idW5kZWZpbmVkIil7bGF6eUFycmF5LmNodW5rc1tjaHVua051bV09ZG9YSFIoc3RhcnQsZW5kKX1pZih0eXBlb2YgbGF6eUFycmF5LmNodW5rc1tjaHVua051bV09PSJ1bmRlZmluZWQiKWFib3J0KCJkb1hIUiBmYWlsZWQhIik7cmV0dXJuIGxhenlBcnJheS5jaHVua3NbY2h1bmtOdW1dfSk7aWYodXNlc0d6aXB8fCFkYXRhbGVuZ3RoKXtjaHVua1NpemU9ZGF0YWxlbmd0aD0xO2RhdGFsZW5ndGg9dGhpcy5nZXR0ZXIoMCkubGVuZ3RoO2NodW5rU2l6ZT1kYXRhbGVuZ3RoO291dCgiTGF6eUZpbGVzIG9uIGd6aXAgZm9yY2VzIGRvd25sb2FkIG9mIHRoZSB3aG9sZSBmaWxlIHdoZW4gbGVuZ3RoIGlzIGFjY2Vzc2VkIil9dGhpcy5fbGVuZ3RoPWRhdGFsZW5ndGg7dGhpcy5fY2h1bmtTaXplPWNodW5rU2l6ZTt0aGlzLmxlbmd0aEtub3duPXRydWV9Z2V0IGxlbmd0aCgpe2lmKCF0aGlzLmxlbmd0aEtub3duKXt0aGlzLmNhY2hlTGVuZ3RoKCl9cmV0dXJuIHRoaXMuX2xlbmd0aH1nZXQgY2h1bmtTaXplKCl7aWYoIXRoaXMubGVuZ3RoS25vd24pe3RoaXMuY2FjaGVMZW5ndGgoKX1yZXR1cm4gdGhpcy5fY2h1bmtTaXplfX1pZihnbG9iYWxUaGlzLlhNTEh0dHBSZXF1ZXN0KXtpZighRU5WSVJPTk1FTlRfSVNfV09SS0VSKWFib3J0KCJDYW5ub3QgZG8gc3luY2hyb25vdXMgYmluYXJ5IFhIUnMgb3V0c2lkZSB3ZWJ3b3JrZXJzIGluIG1vZGVybiBicm93c2Vycy4gVXNlIC0tZW1iZWQtZmlsZSBvciAtLXByZWxvYWQtZmlsZSBpbiBlbWNjIik7dmFyIGxhenlBcnJheT1uZXcgTGF6eVVpbnQ4QXJyYXk7dmFyIHByb3BlcnRpZXM9e2lzRGV2aWNlOmZhbHNlLGNvbnRlbnRzOmxhenlBcnJheX19ZWxzZXt2YXIgcHJvcGVydGllcz17aXNEZXZpY2U6ZmFsc2UsdXJsfX12YXIgbm9kZT1GUy5jcmVhdGVGaWxlKHBhcmVudCxuYW1lLHByb3BlcnRpZXMsY2FuUmVhZCxjYW5Xcml0ZSk7aWYocHJvcGVydGllcy5jb250ZW50cyl7bm9kZS5jb250ZW50cz1wcm9wZXJ0aWVzLmNvbnRlbnRzfWVsc2UgaWYocHJvcGVydGllcy51cmwpe25vZGUuY29udGVudHM9bnVsbDtub2RlLnVybD1wcm9wZXJ0aWVzLnVybH1PYmplY3QuZGVmaW5lUHJvcGVydGllcyhub2RlLHt1c2VkQnl0ZXM6e2dldDpmdW5jdGlvbigpe3JldHVybiB0aGlzLmNvbnRlbnRzLmxlbmd0aH19fSk7dmFyIHN0cmVhbV9vcHM9e307Zm9yKGNvbnN0W2tleSxmbl1vZiBPYmplY3QuZW50cmllcyhub2RlLnN0cmVhbV9vcHMpKXtzdHJlYW1fb3BzW2tleV09KC4uLmFyZ3MpPT57RlMuZm9yY2VMb2FkRmlsZShub2RlKTtyZXR1cm4gZm4oLi4uYXJncyl9fWZ1bmN0aW9uIHdyaXRlQ2h1bmtzKHN0cmVhbSxidWZmZXIsb2Zmc2V0LGxlbmd0aCxwb3NpdGlvbil7dmFyIGNvbnRlbnRzPXN0cmVhbS5ub2RlLmNvbnRlbnRzO2lmKHBvc2l0aW9uPj1jb250ZW50cy5sZW5ndGgpcmV0dXJuIDA7dmFyIHNpemU9TWF0aC5taW4oY29udGVudHMubGVuZ3RoLXBvc2l0aW9uLGxlbmd0aCk7aWYoY29udGVudHMuc2xpY2Upe2Zvcih2YXIgaT0wO2k8c2l6ZTtpKyspe2J1ZmZlcltvZmZzZXQraV09Y29udGVudHNbcG9zaXRpb24raV19fWVsc2V7Zm9yKHZhciBpPTA7aTxzaXplO2krKyl7YnVmZmVyW29mZnNldCtpXT1jb250ZW50cy5nZXQocG9zaXRpb24raSl9fXJldHVybiBzaXplfXN0cmVhbV9vcHMucmVhZD0oc3RyZWFtLGJ1ZmZlcixvZmZzZXQsbGVuZ3RoLHBvc2l0aW9uKT0+e0ZTLmZvcmNlTG9hZEZpbGUobm9kZSk7cmV0dXJuIHdyaXRlQ2h1bmtzKHN0cmVhbSxidWZmZXIsb2Zmc2V0LGxlbmd0aCxwb3NpdGlvbil9O3N0cmVhbV9vcHMubW1hcD0oc3RyZWFtLGxlbmd0aCxwb3NpdGlvbixwcm90LGZsYWdzKT0+e0ZTLmZvcmNlTG9hZEZpbGUobm9kZSk7dmFyIHB0cj1tbWFwQWxsb2MobGVuZ3RoKTtpZighcHRyKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig0OCl9d3JpdGVDaHVua3Moc3RyZWFtLEhFQVA4LHB0cixsZW5ndGgscG9zaXRpb24pO3JldHVybntwdHIsYWxsb2NhdGVkOnRydWV9fTtub2RlLnN0cmVhbV9vcHM9c3RyZWFtX29wcztyZXR1cm4gbm9kZX19O3ZhciBVVEY4VG9TdHJpbmc9KHB0cixtYXhCeXRlc1RvUmVhZCxpZ25vcmVOdWwpPT5wdHI/VVRGOEFycmF5VG9TdHJpbmcoSEVBUFU4LHB0cixtYXhCeXRlc1RvUmVhZCxpZ25vcmVOdWwpOiIiO3ZhciBTWVNDQUxMUz17Y3VycmVudFVtYXNrOjE4LGNhbGN1bGF0ZUF0KGRpcmZkLHBhdGgsYWxsb3dFbXB0eSl7aWYoUEFUSC5pc0FicyhwYXRoKSl7cmV0dXJuIHBhdGh9dmFyIGRpcjtpZihkaXJmZD09PS0xMDApe2Rpcj1GUy5jd2QoKX1lbHNle3ZhciBkaXJzdHJlYW09U1lTQ0FMTFMuZ2V0U3RyZWFtRnJvbUZEKGRpcmZkKTtkaXI9ZGlyc3RyZWFtLnBhdGh9aWYocGF0aC5sZW5ndGg9PTApe2lmKCFhbGxvd0VtcHR5KXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig0NCl9cmV0dXJuIGRpcn1yZXR1cm4gZGlyKyIvIitwYXRofSx3cml0ZVN0YXQoYnVmLHN0YXQpe0hFQVBVMzJbYnVmPj4yXT1zdGF0LmRldjtIRUFQVTMyW2J1Zis0Pj4yXT1zdGF0Lm1vZGU7SEVBUFUzMltidWYrOD4+Ml09c3RhdC5ubGluaztIRUFQVTMyW2J1ZisxMj4+Ml09c3RhdC51aWQ7SEVBUFUzMltidWYrMTY+PjJdPXN0YXQuZ2lkO0hFQVBVMzJbYnVmKzIwPj4yXT1zdGF0LnJkZXY7SEVBUDY0W2J1ZisyND4+M109QmlnSW50KHN0YXQuc2l6ZSk7SEVBUDMyW2J1ZiszMj4+Ml09NDA5NjtIRUFQMzJbYnVmKzM2Pj4yXT1zdGF0LmJsb2Nrczt2YXIgYXRpbWU9c3RhdC5hdGltZS5nZXRUaW1lKCk7dmFyIG10aW1lPXN0YXQubXRpbWUuZ2V0VGltZSgpO3ZhciBjdGltZT1zdGF0LmN0aW1lLmdldFRpbWUoKTtIRUFQNjRbYnVmKzQwPj4zXT1CaWdJbnQoTWF0aC5mbG9vcihhdGltZS8xZTMpKTtIRUFQVTMyW2J1Zis0OD4+Ml09YXRpbWUlMWUzKjFlMyoxZTM7SEVBUDY0W2J1Zis1Nj4+M109QmlnSW50KE1hdGguZmxvb3IobXRpbWUvMWUzKSk7SEVBUFUzMltidWYrNjQ+PjJdPW10aW1lJTFlMyoxZTMqMWUzO0hFQVA2NFtidWYrNzI+PjNdPUJpZ0ludChNYXRoLmZsb29yKGN0aW1lLzFlMykpO0hFQVBVMzJbYnVmKzgwPj4yXT1jdGltZSUxZTMqMWUzKjFlMztIRUFQNjRbYnVmKzg4Pj4zXT1CaWdJbnQoc3RhdC5pbm8pO3JldHVybiAwfSx3cml0ZVN0YXRGcyhidWYsc3RhdHMpe0hFQVBVMzJbYnVmKzQ+PjJdPXN0YXRzLmJzaXplO0hFQVBVMzJbYnVmKzYwPj4yXT1zdGF0cy5ic2l6ZTtIRUFQNjRbYnVmKzg+PjNdPUJpZ0ludChzdGF0cy5ibG9ja3MpO0hFQVA2NFtidWYrMTY+PjNdPUJpZ0ludChzdGF0cy5iZnJlZSk7SEVBUDY0W2J1ZisyND4+M109QmlnSW50KHN0YXRzLmJhdmFpbCk7SEVBUDY0W2J1ZiszMj4+M109QmlnSW50KHN0YXRzLmZpbGVzKTtIRUFQNjRbYnVmKzQwPj4zXT1CaWdJbnQoc3RhdHMuZmZyZWUpO0hFQVBVMzJbYnVmKzQ4Pj4yXT1zdGF0cy5mc2lkO0hFQVBVMzJbYnVmKzY0Pj4yXT1zdGF0cy5mbGFncztIRUFQVTMyW2J1Zis1Nj4+Ml09c3RhdHMubmFtZWxlbn0sZG9Nc3luYyhhZGRyLHN0cmVhbSxsZW4sZmxhZ3Msb2Zmc2V0KXtpZighRlMuaXNGaWxlKHN0cmVhbS5ub2RlLm1vZGUpKXt0aHJvdyBuZXcgRlMuRXJybm9FcnJvcig0Myl9aWYoZmxhZ3MmMil7cmV0dXJuIDB9dmFyIGJ1ZmZlcj1IRUFQVTguc3ViYXJyYXkoYWRkcixhZGRyK2xlbik7RlMubXN5bmMoc3RyZWFtLGJ1ZmZlcixvZmZzZXQsbGVuLGZsYWdzKX0sZ2V0U3RyZWFtRnJvbUZEKGZkKXt2YXIgc3RyZWFtPUZTLmdldFN0cmVhbUNoZWNrZWQoZmQpO3JldHVybiBzdHJlYW19LHZhcmFyZ3M6dW5kZWZpbmVkLGdldFN0cihwdHIpe3ZhciByZXQ9VVRGOFRvU3RyaW5nKHB0cik7cmV0dXJuIHJldH19O2Z1bmN0aW9uIF9mZF9jbG9zZShmZCl7dHJ5e3ZhciBzdHJlYW09U1lTQ0FMTFMuZ2V0U3RyZWFtRnJvbUZEKGZkKTtGUy5jbG9zZShzdHJlYW0pO3JldHVybiAwfWNhdGNoKGUpe2lmKHR5cGVvZiBGUz09InVuZGVmaW5lZCJ8fCEoZS5uYW1lPT09IkVycm5vRXJyb3IiKSl0aHJvdyBlO3JldHVybiBlLmVycm5vfX12YXIgZG9SZWFkdj0oc3RyZWFtLGlvdixpb3ZjbnQsb2Zmc2V0KT0+e3ZhciByZXQ9MDtmb3IodmFyIGk9MDtpPGlvdmNudDtpKyspe3ZhciBwdHI9SEVBUFUzMltpb3Y+PjJdO3ZhciBsZW49SEVBUFUzMltpb3YrND4+Ml07aW92Kz04O3RyeXt2YXIgY3Vycj1GUy5yZWFkKHN0cmVhbSxIRUFQOCxwdHIsbGVuLG9mZnNldCl9Y2F0Y2goZSl7aWYocmV0PjAmJmUgaW5zdGFuY2VvZiBGUy5FcnJub0Vycm9yJiYoZS5lcnJubz09Nnx8ZS5lcnJubz09Nikpe2JyZWFrfXRocm93IGV9aWYoY3VycjwwKXJldHVybi0xO3JldCs9Y3VycjtpZihjdXJyPGxlbilicmVhaztpZih0eXBlb2Ygb2Zmc2V0IT0idW5kZWZpbmVkIil7b2Zmc2V0Kz1jdXJyfX1yZXR1cm4gcmV0fTtmdW5jdGlvbiBfZmRfcmVhZChmZCxpb3YsaW92Y250LHBudW0pe3RyeXt2YXIgc3RyZWFtPVNZU0NBTExTLmdldFN0cmVhbUZyb21GRChmZCk7dmFyIG51bT1kb1JlYWR2KHN0cmVhbSxpb3YsaW92Y250KTtIRUFQVTMyW3BudW0+PjJdPW51bTtyZXR1cm4gMH1jYXRjaChlKXtpZih0eXBlb2YgRlM9PSJ1bmRlZmluZWQifHwhKGUubmFtZT09PSJFcnJub0Vycm9yIikpdGhyb3cgZTtyZXR1cm4gZS5lcnJub319ZnVuY3Rpb24gX2ZkX3NlZWsoZmQsb2Zmc2V0LHdoZW5jZSxuZXdPZmZzZXQpe29mZnNldD1iaWdpbnRUb0k1M0NoZWNrZWQob2Zmc2V0KTt0cnl7aWYoaXNOYU4ob2Zmc2V0KSlyZXR1cm4gMjI7dmFyIHN0cmVhbT1TWVNDQUxMUy5nZXRTdHJlYW1Gcm9tRkQoZmQpO0ZTLmxsc2VlayhzdHJlYW0sb2Zmc2V0LHdoZW5jZSk7SEVBUDY0W25ld09mZnNldD4+M109QmlnSW50KHN0cmVhbS5wb3NpdGlvbik7aWYoc3RyZWFtLmdldGRlbnRzJiYhb2Zmc2V0JiZ3aGVuY2U9PT0wKXN0cmVhbS5nZXRkZW50cz1udWxsO3JldHVybiAwfWNhdGNoKGUpe2lmKHR5cGVvZiBGUz09InVuZGVmaW5lZCJ8fCEoZS5uYW1lPT09IkVycm5vRXJyb3IiKSl0aHJvdyBlO3JldHVybiBlLmVycm5vfX12YXIgZG9Xcml0ZXY9KHN0cmVhbSxpb3YsaW92Y250LG9mZnNldCk9PntpZihpb3ZjbnQ9PTEpe3JldHVybiBGUy53cml0ZShzdHJlYW0sSEVBUDgsSEVBUFUzMltpb3Y+PjJdLEhFQVBVMzJbaW92KzQ+PjJdLG9mZnNldCl9dmFyIHRvdGFsPTA7Zm9yKHZhciBpPTAscD1pb3Y7aTxpb3ZjbnQ7aSsrLHArPTgpe3RvdGFsKz1IRUFQVTMyW3ArND4+Ml19dmFyIHZpZXc9bmV3IFVpbnQ4QXJyYXkodG90YWwpO3ZhciB2b2ZmPTA7Zm9yKHZhciBpPTA7aTxpb3ZjbnQ7aSsrLGlvdis9OCl7dmFyIHB0cj1IRUFQVTMyW2lvdj4+Ml07dmFyIGxlbj1IRUFQVTMyW2lvdis0Pj4yXTt2aWV3LnNldChIRUFQVTguc3ViYXJyYXkocHRyLHB0citsZW4pLHZvZmYpO3ZvZmYrPWxlbn1yZXR1cm4gRlMud3JpdGUoc3RyZWFtLHZpZXcsMCx0b3RhbCxvZmZzZXQpfTtmdW5jdGlvbiBfZmRfd3JpdGUoZmQsaW92LGlvdmNudCxwbnVtKXt0cnl7dmFyIHN0cmVhbT1TWVNDQUxMUy5nZXRTdHJlYW1Gcm9tRkQoZmQpO3ZhciBudW09ZG9Xcml0ZXYoc3RyZWFtLGlvdixpb3ZjbnQpO0hFQVBVMzJbcG51bT4+Ml09bnVtO3JldHVybiAwfWNhdGNoKGUpe2lmKHR5cGVvZiBGUz09InVuZGVmaW5lZCJ8fCEoZS5uYW1lPT09IkVycm5vRXJyb3IiKSl0aHJvdyBlO3JldHVybiBlLmVycm5vfX12YXIgZ2V0Q0Z1bmM9aWRlbnQ9Pnt2YXIgZnVuYz1Nb2R1bGVbIl8iK2lkZW50XTtyZXR1cm4gZnVuY307dmFyIHdyaXRlQXJyYXlUb01lbW9yeT0oYXJyYXksYnVmZmVyKT0+e0hFQVA4LnNldChhcnJheSxidWZmZXIpfTt2YXIgc3RhY2tBbGxvYz1zej0+X19lbXNjcmlwdGVuX3N0YWNrX2FsbG9jKHN6KTt2YXIgc3RyaW5nVG9VVEY4T25TdGFjaz1zdHI9Pnt2YXIgc2l6ZT1sZW5ndGhCeXRlc1VURjgoc3RyKSsxO3ZhciByZXQ9c3RhY2tBbGxvYyhzaXplKTtzdHJpbmdUb1VURjgoc3RyLHJldCxzaXplKTtyZXR1cm4gcmV0fTt2YXIgY2NhbGw9KGlkZW50LHJldHVyblR5cGUsYXJnVHlwZXMsYXJncyxvcHRzKT0+e3ZhciB0b0M9e3N0cmluZzpzdHI9Pnt2YXIgcmV0PTA7aWYoc3RyIT09bnVsbCYmc3RyIT09dW5kZWZpbmVkJiZzdHIhPT0wKXtyZXQ9c3RyaW5nVG9VVEY4T25TdGFjayhzdHIpfXJldHVybiByZXR9LGFycmF5OmFycj0+e3ZhciByZXQ9c3RhY2tBbGxvYyhhcnIubGVuZ3RoKTt3cml0ZUFycmF5VG9NZW1vcnkoYXJyLHJldCk7cmV0dXJuIHJldH19O2Z1bmN0aW9uIGNvbnZlcnRSZXR1cm5WYWx1ZShyZXQpe2lmKHJldHVyblR5cGU9PT0ic3RyaW5nIil7cmV0dXJuIFVURjhUb1N0cmluZyhyZXQpfWlmKHJldHVyblR5cGU9PT0iYm9vbGVhbiIpcmV0dXJuIEJvb2xlYW4ocmV0KTtyZXR1cm4gcmV0fXZhciBmdW5jPWdldENGdW5jKGlkZW50KTt2YXIgY0FyZ3M9W107dmFyIHN0YWNrPTA7aWYoYXJncyl7Zm9yKHZhciBpPTA7aTxhcmdzLmxlbmd0aDtpKyspe3ZhciBjb252ZXJ0ZXI9dG9DW2FyZ1R5cGVzW2ldXTtpZihjb252ZXJ0ZXIpe2lmKCFzdGFjaylzdGFjaz1zdGFja1NhdmUoKTtjQXJnc1tpXT1jb252ZXJ0ZXIoYXJnc1tpXSl9ZWxzZXtjQXJnc1tpXT1hcmdzW2ldfX19dmFyIHJldD1mdW5jKC4uLmNBcmdzKTtmdW5jdGlvbiBvbkRvbmUocmV0KXtpZihzdGFjaylzdGFja1Jlc3RvcmUoc3RhY2spO3JldHVybiBjb252ZXJ0UmV0dXJuVmFsdWUocmV0KX1yZXQ9b25Eb25lKHJldCk7cmV0dXJuIHJldH07RlMuY3JlYXRlUHJlbG9hZGVkRmlsZT1GU19jcmVhdGVQcmVsb2FkZWRGaWxlO0ZTLnByZWxvYWRGaWxlPUZTX3ByZWxvYWRGaWxlO0ZTLnN0YXRpY0luaXQoKTt7aWYoTW9kdWxlWyJub0V4aXRSdW50aW1lIl0pbm9FeGl0UnVudGltZT1Nb2R1bGVbIm5vRXhpdFJ1bnRpbWUiXTtpZihNb2R1bGVbInByaW50Il0pb3V0PU1vZHVsZVsicHJpbnQiXTtpZihNb2R1bGVbInByaW50RXJyIl0pZXJyPU1vZHVsZVsicHJpbnRFcnIiXTtpZihNb2R1bGVbImFyZ3VtZW50cyJdKXByb2dyYW1BcmdzPU1vZHVsZVsiYXJndW1lbnRzIl07aWYoTW9kdWxlWyJ0aGlzUHJvZ3JhbSJdKXRoaXNQcm9ncmFtPU1vZHVsZVsidGhpc1Byb2dyYW0iXTt2YXIgcHJlSW5pdD1Nb2R1bGVbInByZUluaXQiXTtpZihwcmVJbml0KXtpZih0eXBlb2YgcHJlSW5pdD09ImZ1bmN0aW9uIilNb2R1bGVbInByZUluaXQiXT1wcmVJbml0PVtwcmVJbml0XTt3aGlsZShwcmVJbml0Lmxlbmd0aD4wKXtwcmVJbml0LnNoaWZ0KCkoKX19fU1vZHVsZVsiY2NhbGwiXT1jY2FsbDt2YXIgX2FuYWx5emUsX19lbXNjcmlwdGVuX3N0YWNrX3Jlc3RvcmUsX19lbXNjcmlwdGVuX3N0YWNrX2FsbG9jLF9lbXNjcmlwdGVuX3N0YWNrX2dldF9jdXJyZW50LG1lbW9yeSxfX2luZGlyZWN0X2Z1bmN0aW9uX3RhYmxlLHdhc21NZW1vcnk7ZnVuY3Rpb24gYXNzaWduV2FzbUV4cG9ydHMod2FzbUV4cG9ydHMpe19hbmFseXplPU1vZHVsZVsiX2FuYWx5emUiXT13YXNtRXhwb3J0c1sibSJdO19fZW1zY3JpcHRlbl9zdGFja19yZXN0b3JlPXdhc21FeHBvcnRzWyJuIl07X19lbXNjcmlwdGVuX3N0YWNrX2FsbG9jPXdhc21FeHBvcnRzWyJvIl07X2Vtc2NyaXB0ZW5fc3RhY2tfZ2V0X2N1cnJlbnQ9d2FzbUV4cG9ydHNbInAiXTttZW1vcnk9d2FzbU1lbW9yeT13YXNtRXhwb3J0c1siayJdO19faW5kaXJlY3RfZnVuY3Rpb25fdGFibGU9d2FzbUV4cG9ydHNbIl9faW5kaXJlY3RfZnVuY3Rpb25fdGFibGUiXX12YXIgd2FzbUltcG9ydHM9e2E6X19fY3hhX3Rocm93LGo6X19hYm9ydF9qcyxnOl9jbG9ja190aW1lX2dldCxoOl9lbXNjcmlwdGVuX3Jlc2l6ZV9oZWFwLGk6X2Vudmlyb25fZ2V0LGM6X2Vudmlyb25fc2l6ZXNfZ2V0LGQ6X2ZkX2Nsb3NlLGU6X2ZkX3JlYWQsZjpfZmRfc2VlayxiOl9mZF93cml0ZX07YXN5bmMgZnVuY3Rpb24gcnVuKCl7cHJlUnVuKCk7aWYocnVuRGVwZW5kZW5jaWVzKXthd2FpdCByZXNvbHZlUnVuRGVwZW5kZW5jaWVzKCl9dmFyIHNldFN0YXR1cz1Nb2R1bGVbInNldFN0YXR1cyJdO2lmKHNldFN0YXR1cyl7c2V0U3RhdHVzKCJSdW5uaW5nLi4uIik7YXdhaXQgbmV3IFByb21pc2UocmVzb2x2ZT0+c2V0VGltZW91dChyZXNvbHZlLDEpKTtzZXRUaW1lb3V0KHNldFN0YXR1cywxLCIiKX1pZihBQk9SVClyZXR1cm47aW5pdFJ1bnRpbWUoKTtNb2R1bGVbIm9uUnVudGltZUluaXRpYWxpemVkIl0/LigpO3Bvc3RSdW4oKX12YXIgd2FzbUV4cG9ydHM7d2FzbUV4cG9ydHM9YXdhaXQgY3JlYXRlV2FzbSgpO2F3YWl0IHJ1bigpOwo7cmV0dXJuIE1vZHVsZX19KSgpO2lmKHR5cGVvZiBleHBvcnRzPT09Im9iamVjdCImJnR5cGVvZiBtb2R1bGU9PT0ib2JqZWN0Iil7bW9kdWxlLmV4cG9ydHM9VGl0YW40UDttb2R1bGUuZXhwb3J0cy5kZWZhdWx0PVRpdGFuNFB9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09ImZ1bmN0aW9uIiYmZGVmaW5lWyJhbWQiXSlkZWZpbmUoW10sKCk9PlRpdGFuNFApOwo=';

  coachWorker(); // 先把后台线程起好
  loadModel();   // 下载（或取出存着的）权重，交给后台线程解好，第一段讲解就不用等
  if (!/^\/variants\//.test(location.pathname)) loadStockfish(); // 本地引擎也先加载好：在线引擎一超时就能马上接手（四人象棋用自己的引擎，不需要）
  render();
  setInterval(tick, 400);
})();
