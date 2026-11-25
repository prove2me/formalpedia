-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_setLIntegral_image_881958a63272
-- name    : P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_setLIntegral_image_881958a63272
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:33.061389+00:00
-- url     : https://prove2.me/theorems/2efa3778-27fe-4a2f-8355-8420b13e6237
-- title:
--   P2 M Ground Theory Heights  Heights Area Formula Local set LIntegral image 881958a63272: P2 M Ground Theory Heights  Heights Area Formula Local set LIntegral image 881958a63272
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Formula Local set LIntegral image 881958a63272 construction uses the P2 M Ground Theory Heights  Heights Area Formula Local set LIntegral image 881958a63272 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAreaFormulaLocal.lean#L51-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAreaFormulaLocal.lean#L51-L81

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

theorem P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_setLIntegral_image_881958a63272 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (hk : finrank ℝ E = k)
    {B : Set E} (hB : MeasurableSet B) {a : E → EuclideanSpace ℝ (Fin k)}
    {a' : E → E →L[ℝ] EuclideanSpace ℝ (Fin k)} (ha' : ∀ x ∈ B, HasFDerivWithinAt a (a' x) B x)
    (hinj : InjOn a B) (g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞) :
    ∫⁻ y in a '' B, g y ∂(μH[(k : ℝ)]) =
      ∫⁻ x in B, g (a x) *
        ENNReal.ofReal (a' x : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet ∂(μH[(k : ℝ)]) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaFormulaLocal».«setLIntegral_image» := P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_setLIntegral_image_881958a63272
