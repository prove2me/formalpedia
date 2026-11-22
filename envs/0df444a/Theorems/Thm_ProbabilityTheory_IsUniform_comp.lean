-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_comp
-- name    : ProbabilityTheory.IsUniform.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:23:25.857603+00:00
-- url     : https://prove2.me/theorems/ae937cb0-8826-4fc4-b6fe-9154404ffd77
-- title:
--   Is Uniform: comp
-- statement:
--   The image of a uniform random variable under an injective map is uniform on the image.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L84-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L84-L94

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

theorem ProbabilityTheory.IsUniform.comp
    [DecidableEq T] {H : Finset S} (h : IsUniform H X μ) {f : S → T}
    (hf : Injective f) : IsUniform (Finset.image f H) (f ∘ X) μ := by sorry
