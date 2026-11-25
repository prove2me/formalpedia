-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_zero_be1159debaaa
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_zero_be1159debaaa
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:55.234009+00:00
-- url     : https://prove2.me/theorems/68055278-cae6-469d-be9e-8c327c318db4
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece norm pair Pt zero be1159debaaa: P2 M Ground Theory Heights  Heights Area Graph Piece norm pair Pt zero be1159debaaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece norm pair Pt zero be1159debaaa construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece norm pair Pt zero be1159debaaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L62-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.AreaGraphPiece
variable {k m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_zero_be1159debaaa (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt (0 : EuclideanSpace ℝ (Fin k)) w‖ = ‖w‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«norm_pairPt_zero» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_zero_be1159debaaa
