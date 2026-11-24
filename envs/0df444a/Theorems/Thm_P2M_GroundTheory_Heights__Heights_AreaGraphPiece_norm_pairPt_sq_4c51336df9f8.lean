-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_sq_4c51336df9f8
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_sq_4c51336df9f8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:49.043808+00:00
-- url     : https://prove2.me/theorems/a4237fde-851c-4d11-b3a6-1ea31242c85e
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece norm pair Pt sq 4c51336df9f8: P2 M Ground Theory Heights  Heights Area Graph Piece norm pair Pt sq 4c51336df9f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece norm pair Pt sq 4c51336df9f8 construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece norm pair Pt sq 4c51336df9f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L52-L55

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

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_sq_4c51336df9f8 (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt u w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«norm_pairPt_sq» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_sq_4c51336df9f8
