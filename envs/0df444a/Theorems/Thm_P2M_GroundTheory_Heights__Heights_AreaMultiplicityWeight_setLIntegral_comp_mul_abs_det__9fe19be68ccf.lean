-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaMultiplicityWeight_setLIntegral_comp_mul_abs_det__9fe19be68ccf
-- name    : P2M_GroundTheory_Heights__Heights_AreaMultiplicityWeight_setLIntegral_comp_mul_abs_det__9fe19be68ccf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:17.496454+00:00
-- url     : https://prove2.me/theorems/b67fa485-fbdc-480f-900b-1befaccd8200
-- title:
--   P2 M Ground Theory Heights  Heights Area Multiplicity Weight set LIntegral comp mul abs det  9fe19be68ccf: P2 M Ground Theory Heights  Heights Area Multiplicity Weight set LIntegral comp mul abs det
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Multiplicity Weight set LIntegral comp mul abs det  9fe19be68ccf construction uses the P2 M Ground Theory Heights  Heights Area Multiplicity Weight set LIntegral comp mul abs det  9fe19be68ccf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAreaMultiplicityWeight.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAreaMultiplicityWeight.lean#L14-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaMultiplicityWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
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
open MeasureTheory Module Set Filter Function
open scoped ENNReal NNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AreaMultiplicityWeight_setLIntegral_comp_mul_abs_det__9fe19be68ccf {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : NullMeasurableSet s μ) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ = ∫⁻ y in f '' s, g y ∂μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaMultiplicityWeight».«setLIntegral_comp_mul_abs_det₀» := P2M_GroundTheory_Heights__Heights_AreaMultiplicityWeight_setLIntegral_comp_mul_abs_det__9fe19be68ccf
