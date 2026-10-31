-- Prove2me | Theorems.Thm_TetrisHard_Rows_single_bucket_sequence
-- name    : TetrisHard.Rows.single_bucket_sequence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:57:03.308334+00:00
-- url     : https://prove2.me/theorems/e5c71a07-a418-4ae4-9a6f-a34399fc722f
-- title:
--   Lemma 5.14 — Each integer block stays in one bucket for every r ≥ 0
-- statement:
--   Lemma 5.14 For any r ≥0, in an unprepped configuration, the only possibly valid strategy for the sequence I, LG, Sq, r × ⟨LG, LS, LG, LG, Sq⟩, Sq, Sq is to place all of the pieces into a single bucket, yielding an unprepped configuration.
--
--   For every natural r, including zero, a valid segment consisting of I, LG, Sq, then r copies of LG, LS, LG, LG, Sq, then Sq, Sq, starting in an unprepped configuration of a valid normalized base game, places all pieces in one bucket and leaves the entire configuration unprepped.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
--   - encoding: a move is valid when it can occur in a winning trajectory sequence → a reachable prefix, this segment, and a winning suffix in the prescribed input list; reason: the existence of a continuation is expressed operationally without assuming canonical placements
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Lemma 5.14, printed p. 17 = PDF p. 17, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem single_bucket_sequence (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (pre seg : List PieceState) (B B' : Board)
    (hseg : ValidSegment R P (stagingAllowance R) pre seg B B') (r : ℕ)
    (htypes : seg.map PieceState.kind = integerBlock r)
    (hshape : AllUnprepped B P.s (baseHeight P)) :
    ∃ j : Fin P.s, (∀ q ∈ seg, InBucket j.val q) ∧ AllUnprepped B' P.s (baseHeight P) := by sorry

end TetrisHard.Rows
