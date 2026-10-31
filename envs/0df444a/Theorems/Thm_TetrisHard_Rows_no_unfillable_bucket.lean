-- Prove2me | Theorems.Thm_TetrisHard_Rows_no_unfillable_bucket
-- name    : TetrisHard.Rows.no_unfillable_bucket
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:57:06.861787+00:00
-- url     : https://prove2.me/theorems/54d0f8a9-aec6-4f9b-9817-fd67b1011d62
-- title:
--   Lemma 5.7 — Winning play never produces an unfillable bucket
-- statement:
--   Lemma 5.7 In any valid strategy, no configuration with an unfillable bucket arises.
--
--   For every configuration on a winning continuation of a valid normalized base game, each bucket is fillable. If v rows have already been cleared, its remaining original height is H−v. Fillability uses arbitrary finite sequences from {LG,LS,Sq,I}, actual trajectories, and no further row deletions.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: the normalized reduction and its fixed O(1) staging term → the three source normalization conditions and staging 2R.radius+8; reason: normalization is restricted to reduction lemmas; a fixed explicit allowance replaces asymptotic notation, with sufficiency asserted by completeness
--   - encoding: a move is valid when it can occur in a winning trajectory sequence → a reachable prefix, this segment, and a winning suffix in the prescribed input list; reason: the existence of a continuation is expressed operationally without assuming canonical placements
--   - encoding: configurations along a winning strategy → remaining bucket height H−v after v deletions; reason: the original bucket rows shrink under simultaneous row compression; a fully cleared bucket has remaining height zero
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Lemma 5.7, printed p. 13 = PDF p. 13, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem no_unfillable_bucket (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (pre seg : List PieceState) (B B' : Board)
    (hseg : ValidSegment R P (stagingAllowance R) pre seg B B') :
    ∀ v, Play R (baseBoard P (stagingAllowance R)) (basePieces P) pre B v →
      ∀ j : Fin P.s, ¬ Unfillable R B j.val (baseHeight P - v) := by sorry

end TetrisHard.Rows
