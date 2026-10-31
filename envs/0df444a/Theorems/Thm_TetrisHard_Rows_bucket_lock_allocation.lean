-- Prove2me | Theorems.Thm_TetrisHard_Rows_bucket_lock_allocation
-- name    : TetrisHard.Rows.bucket_lock_allocation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:30.995531+00:00
-- url     : https://prove2.me/theorems/d4a98501-ba5d-4420-8452-f5e908b45e92
-- title:
--   Corollary 5.6 — Both bucket/lock allocation clauses
-- statement:
--   Corollary 5.6 In any valid strategy: 1. all gridsquares of all pieces preceding the RG must all be placed into buckets, filling all empty bucket gridsquares. 2. all gridsquares of all pieces starting with (and including) the RG must be placed into the lock columns, filling all empty lock gridsquares.
--
--   Fix the same source rotation model and normalized reduction input. In every winning play, all pieces before RG lie in bucket columns and the pre-RG board has every bucket full through H. All pieces starting with RG lie in the lock columns, and the final board is empty. The pre-RG part clears no rows.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
--   - encoding: filling all empty bucket and lock gridsquares → full buckets at the pre-RG boundary and an empty final board, with both placement clauses; reason: lock rows shift after deletions; final occupancy expresses their complete filling and clearing without identifying old rows with new coordinates
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Corollary 5.6, printed p. 12 = PDF p. 12, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem bucket_lock_allocation (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (qs : List PieceState) (B : Board)
    (hvalid : ValidStrategy R P (stagingAllowance R) qs B) :
    BucketLockAllocation R P (stagingAllowance R) qs B := by sorry

end TetrisHard.Rows
