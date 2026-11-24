-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_graphLin_apply_abc67cdea5c9
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_graphLin_apply_abc67cdea5c9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:20.703808+00:00
-- url     : https://prove2.me/theorems/6c0ce465-1f64-43da-8047-4f9aea1a014f
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece graph Lin apply abc67cdea5c9: P2 M Ground Theory Heights  Heights Area Graph Piece graph Lin apply abc67cdea5c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece graph Lin apply abc67cdea5c9 construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece graph Lin apply abc67cdea5c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L74-L75

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

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_graphLin_apply_abc67cdea5c9 (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : graphLin A x = pairPt x (A x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«graphLin_apply» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_graphLin_apply_abc67cdea5c9
