-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_nonempty_preimage_of_mem
-- name    : ProbabilityTheory.IsUniform.nonempty_preimage_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:35.006579+00:00
-- url     : https://prove2.me/theorems/62fe14e0-5183-4bfa-b11e-48eaf6cccbb3
-- title:
--   Is Uniform: nonempty preimage of mem
-- statement:
--   The Is Uniform construction uses the nonempty preimage of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L215-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L215-L220

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

theorem ProbabilityTheory.IsUniform.nonempty_preimage_of_mem
    [NeZero μ] {H : Finset S} (h : IsUniform H X μ)
    (hX : Measurable X) {s : S} (hs : s ∈ H) : Set.Nonempty (X ⁻¹' {s}) := by sorry
