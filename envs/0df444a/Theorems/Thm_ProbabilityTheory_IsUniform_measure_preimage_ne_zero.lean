-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage_ne_zero
-- name    : ProbabilityTheory.IsUniform.measure_preimage_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:46.518681+00:00
-- url     : https://prove2.me/theorems/b5c3491d-c4d4-46b2-8102-1889ef74e49a
-- title:
--   Is Uniform: measure preimage ne zero
-- statement:
--   $\mathbb{P}(U_H \in H') \neq 0$ if $H'$ intersects $H$ and the measure is non-zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L246-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L246-L252

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem ProbabilityTheory.IsUniform.measure_preimage_ne_zero
    {H : Finset S} [NeZero μ] (h : IsUniform H X μ)
    (hX : Measurable X) {H' : Set S} (h' : (H' ∩ H).Nonempty) : μ (X ⁻¹' H') ≠ 0 := by sorry
