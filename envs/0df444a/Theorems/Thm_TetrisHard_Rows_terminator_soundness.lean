-- Prove2me | Theorems.Thm_TetrisHard_Rows_terminator_soundness
-- name    : TetrisHard.Rows.terminator_soundness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:52.292765+00:00
-- url     : https://prove2.me/theorems/987ac86b-c4bf-4685-81dc-d6e4aacd737a
-- title:
--   Lemma 5.13 — Both terminator cases
-- statement:
--   Lemma 5.13 (Terminator Soundness) For the sequence ⟨Sq, Sq⟩, 1. In a one-overflat configuration, the only possibly valid strategy is to place both pieces in the overflat bucket to produce an unprepped bucket, yielding an unprepped configuration. 2. In a one-tall-plateau-one-trigger-happy configuration, there is no valid strategy.
--
--   In a valid normalized base game, a valid pair of squares starting in a one-overflat configuration must both enter its overflat bucket and leave every bucket unprepped. A one-tall-plateau-one-trigger-happy configuration admits no valid pair of squares. Both clauses use the same admissible reasonable rotation model.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
--   - encoding: a move is valid when it can occur in a winning trajectory sequence → a reachable prefix, this segment, and a winning suffix in the prescribed input list; reason: the existence of a continuation is expressed operationally without assuming canonical placements
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Lemma 5.13, printed p. 17 = PDF p. 17, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem terminator_soundness (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (pre seg : List PieceState) (B B' : Board)
    (hseg : ValidSegment R P (stagingAllowance R) pre seg B B')
    (htypes : seg.map PieceState.kind = terminator) :
    (∀ j : Fin P.s, One Overflat B P.s (baseHeight P) j →
      (∀ q ∈ seg, InBucket j.val q) ∧ AllUnprepped B' P.s (baseHeight P)) ∧
    (∀ j k : Fin P.s, ¬ OneEach TallPlateau TriggerHappy B P.s (baseHeight P) j k) := by sorry

end TetrisHard.Rows
