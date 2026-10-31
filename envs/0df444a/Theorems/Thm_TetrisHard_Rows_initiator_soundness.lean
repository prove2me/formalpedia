-- Prove2me | Theorems.Thm_TetrisHard_Rows_initiator_soundness
-- name    : TetrisHard.Rows.initiator_soundness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:57:24.942993+00:00
-- url     : https://prove2.me/theorems/e995b596-5b58-434e-ad2b-f5fc17b06fe7
-- title:
--   Lemma 5.11 — Initiator soundness
-- statement:
--   Lemma 5.11 (Initiator Soundness) In an unprepped configuration, the only possibly valid strategy for ⟨I, LG, Sq⟩is to place all three pieces in some bucket to produce an overflat bucket, yielding a one-overflat configuration.
--
--   In a valid normalized base game with a fixed admissible reasonable model, consider a segment of a winning play whose types are I, LG, Sq. If its starting configuration is unprepped, all three pieces occupy one bucket, and the resulting configuration has that bucket overflat and all others unprepped.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
--   - encoding: a move is valid when it can occur in a winning trajectory sequence → a reachable prefix, this segment, and a winning suffix in the prescribed input list; reason: the existence of a continuation is expressed operationally without assuming canonical placements
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Lemma 5.11, printed p. 17 = PDF p. 17, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem initiator_soundness (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (pre seg : List PieceState) (B B' : Board)
    (hseg : ValidSegment R P (stagingAllowance R) pre seg B B')
    (htypes : seg.map PieceState.kind = initiator)
    (hshape : AllUnprepped B P.s (baseHeight P)) :
    ∃ j : Fin P.s, (∀ q ∈ seg, InBucket j.val q) ∧ One Overflat B' P.s (baseHeight P) j := by sorry

end TetrisHard.Rows
