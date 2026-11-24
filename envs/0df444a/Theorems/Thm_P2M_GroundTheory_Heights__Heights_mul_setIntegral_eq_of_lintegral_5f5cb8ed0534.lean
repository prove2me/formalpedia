-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_5f5cb8ed0534
-- name    : P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_5f5cb8ed0534
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:50.451797+00:00
-- url     : https://prove2.me/theorems/eb6d2514-8f1a-4526-9317-36b6b12b8539
-- title:
--   P2 M Ground Theory Heights  Heights mul set Integral eq of lintegral 5f5cb8ed0534: P2 M Ground Theory Heights  Heights mul set Integral eq of lintegral 5f5cb8ed0534
-- statement:
--   The P2 M Ground Theory Heights  Heights mul set Integral eq of lintegral 5f5cb8ed0534 construction uses the P2 M Ground Theory Heights  Heights mul set Integral eq of lintegral 5f5cb8ed0534 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L132-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L132-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder
variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace X]

theorem P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_5f5cb8ed0534 {μ : Measure E} {ν : Measure X} {C : Set E}
    {fib : X → Set W} (hfin : ∀ x, (fib x).Finite) (v : X → W → E) (ρ : X → W → ℂ → ℝ)
    (hρ : ∀ x w t, 0 ≤ ρ x w t) (hρc : ∀ x w, Continuous (ρ x w))
    {c : ℝ} (hc : 0 ≤ c) {b : ℝ≥0∞} (hb : b ≠ 0)
    (hA : ∀ F : E → ℝ≥0∞, Measurable F →
      AEMeasurable (fun x => ∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ν ∧
      ENNReal.ofReal c * ∫⁻ y in C, F y ∂μ =
        b * ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ∂ν)
    {f : E → ℝ} (hf : IntegrableOn f C μ) :
    c * ∫ y in C, f y ∂μ =
      b.toReal * ∫ x, (∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) ∂ν := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mul_setIntegral_eq_of_lintegral» := P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_5f5cb8ed0534
