-- Prove2me | Theorems.Thm_TetrisHard_Rows_reduction_polynomial_size
-- name    : TetrisHard.Rows.reduction_polynomial_size
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:19.650278+00:00
-- url     : https://prove2.me/theorems/326e04e8-55b8-4bd8-b563-a1a46a8a5c58
-- title:
--   Theorem 3.2 — Polynomial size of the explicit reduction
-- statement:
--   Theorem 3.2 The game G(P) is polynomial in the size of P.
--
--   For each fixed staging allowance, there are natural constants C and k, independent of P, such that the explicit encoded length of G(P) is at most C(|code(P)|+1)^k for every valid normalized input P. This is a size statement, not an assumption of polynomial-time constructibility.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: size polynomial in the unary input → a uniform bound C(|code(P)|+1)^k on explicit game codes; reason: the finite binary encoding writes all cells and pieces, with constants chosen before the input
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Theorem 3.2, printed p. 9 = PDF p. 9, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem reduction_polynomial_size (staging : ℕ) :
    ∃ C k : ℕ, ∀ P : ThreePartition, P.Valid → P.Normalized →
      (baseGame P staging).code.length ≤ C * (P.code.length + 1) ^ k := by sorry

end TetrisHard.Rows
