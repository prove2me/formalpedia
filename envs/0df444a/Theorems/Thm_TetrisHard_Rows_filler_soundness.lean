-- Prove2me | Theorems.Thm_TetrisHard_Rows_filler_soundness
-- name    : TetrisHard.Rows.filler_soundness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:57:16.051732+00:00
-- url     : https://prove2.me/theorems/0c082a9d-4d83-40a4-8b5f-58fe2deb49ce
-- title:
--   Lemma 5.12 — Both filler cases
-- statement:
--   Lemma 5.12 (Filler Soundness) For the sequence ⟨LG, LS, LG, LG, Sq⟩: 1. In a one-overflat configuration, the only possibly valid strategy is either (1) to place all pieces in the overflat bucket to produce an overflat bucket, yielding a one-overflat configuration, or (2) to place ⟨LG, LS⟩into the overflat bucket and ⟨LG, LG, Sq⟩in an unprepped bucket, yielding a one-tall-plateau-one-trigger-happy configuration. 2. In a one-tall-plateau-one-trigger-happy configuration, there is no valid strategy.
--
--   In a valid normalized base game, consider a valid LG, LS, LG, LG, Sq segment. From a one-overflat configuration, either every piece enters the original overflat bucket and it remains overflat, or LG, LS enter that bucket and LG, LG, Sq enter a distinct initially unprepped bucket, producing respectively trigger-happy and tall-plateau buckets, with all others unprepped. A one-tall-plateau-one-trigger-happy starting configuration admits no such valid segment. These are both clauses, not alternatives in the assumptions.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
--   - encoding: a move is valid when it can occur in a winning trajectory sequence → a reachable prefix, this segment, and a winning suffix in the prescribed input list; reason: the existence of a continuation is expressed operationally without assuming canonical placements
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Lemma 5.12, printed p. 17 = PDF p. 17, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem filler_soundness (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (pre seg : List PieceState) (B B' : Board)
    (hseg : ValidSegment R P (stagingAllowance R) pre seg B B')
    (htypes : seg.map PieceState.kind = filler) :
    (∀ j : Fin P.s, One Overflat B P.s (baseHeight P) j →
      ((∀ q ∈ seg, InBucket j.val q) ∧ One Overflat B' P.s (baseHeight P) j) ∨
      (∃ k : Fin P.s, j ≠ k ∧ Unprepped B k.val (baseHeight P) ∧
        (∀ q ∈ seg.take 2, InBucket j.val q) ∧
        (∀ q ∈ seg.drop 2, InBucket k.val q) ∧
        OneEach TallPlateau TriggerHappy B' P.s (baseHeight P) k j)) ∧
    (∀ j k : Fin P.s, ¬ OneEach TallPlateau TriggerHappy B P.s (baseHeight P) j k) := by sorry

end TetrisHard.Rows
