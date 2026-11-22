-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_nonempty
-- name    : ProbabilityTheory.IsUniform.nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:22.808795+00:00
-- url     : https://prove2.me/theorems/0d3990b4-522d-4f73-ac04-bbd442a3156a
-- title:
--   Is Uniform: nonempty
-- statement:
--   Uniform random variables only exist for non-empty sets H.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L126-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L126-L130

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

theorem ProbabilityTheory.IsUniform.nonempty
    {H : Finset S} (h : IsUniform H X μ) [hμ : NeZero μ] : H.Nonempty := by sorry
