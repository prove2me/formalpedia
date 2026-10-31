-- Prove2me | Theorems.Thm_TetrisHard_Rows_completeness
-- name    : TetrisHard.Rows.completeness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:50.85442+00:00
-- url     : https://prove2.me/theorems/d9e909d3-00c6-4a9a-8ba8-fe2f71d829f3
-- title:
--   Theorem 4.1 — Completeness of the base game
-- statement:
--   Theorem 4.1 (Completeness) For any “yes” instance P of 3-Partition, there is a trajectory sequence Σ that clears the entire gameboard of G(P) without triggering a loss.
--
--   Fix an admissible reasonable rotation model and a valid normalized input P. If P has a solution, some play places the entire prescribed sequence, clears H=6T+22 rows, and ends on an empty board. Every trajectory has a clear prescribed spawn, so the full sequence incurs no loss. The printed empty-input case is retained; see insight I2.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Theorem 4.1, printed p. 10 = PDF p. 10, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem completeness (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hyes : P.HasSolution) :
    ∃ qs B, Play R (baseBoard P (stagingAllowance R)) (basePieces P) qs B (baseHeight P) ∧
      qs.length = (basePieces P).length ∧ B.Empty := by sorry

end TetrisHard.Rows
