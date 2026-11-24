-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_normDet_graphLin_eb5fb2a3868a
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_normDet_graphLin_eb5fb2a3868a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:26.832683+00:00
-- url     : https://prove2.me/theorems/06c20f00-739b-41da-9220-b6f612aa5300
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece norm Det graph Lin eb5fb2a3868a: P2 M Ground Theory Heights  Heights Area Graph Piece norm Det graph Lin eb5fb2a3868a
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece norm Det graph Lin eb5fb2a3868a construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece norm Det graph Lin eb5fb2a3868a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L91-L97

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

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_normDet_graphLin_eb5fb2a3868a (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (graphLin A).normDet =
      graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«normDet_graphLin» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_normDet_graphLin_eb5fb2a3868a
