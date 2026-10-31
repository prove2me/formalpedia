-- Prove2me | Theorems.Thm_TetrisHard_Rows_final_bucket_filling
-- name    : TetrisHard.Rows.final_bucket_filling
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:47.609481+00:00
-- url     : https://prove2.me/theorems/dd121189-2145-4d69-be0a-239d84a8cfa2
-- title:
--   Proposition 5.15 — Final I pieces force exactly four empty cells per bucket
-- statement:
--   Proposition 5.15 Consider an unprepped configuration with exactly 4s total unfilled gridsquares in all buckets. Then there is a winning strategy for s successive I’s only if there are exactly four unfilled gridsquares per bucket, and this strategy is to place one in each bucket to fill it up to the (6T + 22)nd row.
--
--   In a valid normalized base game, suppose a valid segment of s successive I pieces starts with every bucket unprepped and exactly 4s empty cells in the buckets. Then every bucket initially has exactly four empty cells; exactly one of the segment’s piece positions belongs to each bucket; and every bucket is filled through row H=6T+22 afterward.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
--   - encoding: a move is valid when it can occur in a winning trajectory sequence → a reachable prefix, this segment, and a winning suffix in the prescribed input list; reason: the existence of a continuation is expressed operationally without assuming canonical placements
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Proposition 5.15, printed p. 18 = PDF p. 18, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem final_bucket_filling (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (pre seg : List PieceState) (B B' : Board)
    (hseg : ValidSegment R P (stagingAllowance R) pre seg B B')
    (htypes : seg.map PieceState.kind = List.replicate P.s .I)
    (hshape : AllUnprepped B P.s (baseHeight P))
    (hcount : (∑ j : Fin P.s, emptyBucketCells B j.val (baseHeight P)) = 4 * P.s) :
    (∀ j : Fin P.s, emptyBucketCells B j.val (baseHeight P) = 4) ∧
    (∀ j : Fin P.s, ∃! i : Fin seg.length, InBucket j.val (seg.get i)) ∧
    (∀ j : Fin P.s, BucketFull B' j.val (baseHeight P)) := by sorry

end TetrisHard.Rows
