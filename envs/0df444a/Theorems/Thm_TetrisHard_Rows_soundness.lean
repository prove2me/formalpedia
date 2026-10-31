-- Prove2me | Theorems.Thm_TetrisHard_Rows_soundness
-- name    : TetrisHard.Rows.soundness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:51.72399+00:00
-- url     : https://prove2.me/theorems/2e0c5bf8-0b40-44ee-b28d-4dc83dd23ec3
-- title:
--   Theorem 5.16 — Soundness of the base reduction
-- statement:
--   Theorem 5.16 (Soundness) If there is a valid strategy for G(P), then P is a “yes” instance of 3-Partition.
--
--   For any admissible reasonable rotation model and any valid normalized 3-Partition input, the existence of a strategy clearing H rows of the base game implies that the indexed input has a 3-partition.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Theorem 5.16, printed p. 18 = PDF p. 18, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem soundness (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized)
    (hvalid : ∃ qs B, ValidStrategy R P (stagingAllowance R) qs B) :
    P.HasSolution := by sorry

end TetrisHard.Rows
