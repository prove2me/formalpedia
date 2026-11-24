-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_normDet_comp_of_norm_ca1a2bf1be84
-- name    : P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_normDet_comp_of_norm_ca1a2bf1be84
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:18.243596+00:00
-- url     : https://prove2.me/theorems/4e34bc4c-6d84-4e7a-86c9-f3ca86eb1235
-- title:
--   P2 M Ground Theory Heights  Heights Area Formula Local norm Det comp of norm ca1a2bf1be84: P2 M Ground Theory Heights  Heights Area Formula Local norm Det comp of norm ca1a2bf1be84
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Formula Local norm Det comp of norm ca1a2bf1be84 construction uses the P2 M Ground Theory Heights  Heights Area Formula Local norm Det comp of norm ca1a2bf1be84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAreaFormulaLocal.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAreaFormulaLocal.lean#L21-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaFormulaLocal
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
open MeasureTheory Module Set
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.AreaFormulaLocal

theorem P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_normDet_comp_of_norm_ca1a2bf1be84 {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (Q : F →ₗ[ℝ] G) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    (Q ∘ₗ M).normDet = M.normDet := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaFormulaLocal».«normDet_comp_of_norm» := P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_normDet_comp_of_norm_ca1a2bf1be84
