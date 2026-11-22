-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_measureReal_preimage_of_mem
-- name    : ProbabilityTheory.IsUniform.measureReal_preimage_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:23.073662+00:00
-- url     : https://prove2.me/theorems/fda2ff92-1ee0-4d89-9cab-9ae6e34cc6d8
-- title:
--   Is Uniform: measure Real preimage of mem
-- statement:
--   A "unit test" for the definition of uniform distribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L178-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L178-L182

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

theorem ProbabilityTheory.IsUniform.measureReal_preimage_of_mem
    {A : Finset S} [IsProbabilityMeasure μ]
    (h : IsUniform A X μ) (hX : Measurable X) {s : S} (hs : s ∈ A) :
    μ.real (X ⁻¹' {s}) = 1 / A.card := by sorry
