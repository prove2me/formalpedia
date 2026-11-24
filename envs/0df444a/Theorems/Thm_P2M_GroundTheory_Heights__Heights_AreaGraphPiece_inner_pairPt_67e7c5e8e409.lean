-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_inner_pairPt_67e7c5e8e409
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_inner_pairPt_67e7c5e8e409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:55.928241+00:00
-- url     : https://prove2.me/theorems/6590447f-e570-4108-aeee-0d40a1edcc78
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece inner pair Pt 67e7c5e8e409: P2 M Ground Theory Heights  Heights Area Graph Piece inner pair Pt 67e7c5e8e409
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece inner pair Pt 67e7c5e8e409 construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece inner pair Pt 67e7c5e8e409 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L48-L50

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

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_inner_pairPt_67e7c5e8e409 (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    ⟪pairPt u w, pairPt u' w'⟫ = ⟪u, u'⟫ + ⟪w, w'⟫ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«inner_pairPt» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_inner_pairPt_67e7c5e8e409
