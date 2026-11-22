-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_of_identDistrib
-- name    : ProbabilityTheory.IsUniform.of_identDistrib
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:46.672821+00:00
-- url     : https://prove2.me/theorems/78a54bfb-951d-4ac3-851e-3723e0f65e29
-- title:
--   Is Uniform: of ident Distrib
-- statement:
--   A copy of a uniform random variable is also uniform.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L230-L241
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L230-L241

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

theorem ProbabilityTheory.IsUniform.of_identDistrib
    {Ω' : Type*} [MeasurableSpace Ω'] (h : IsUniform H X μ)
    {X' : Ω'
      → S} {μ' : Measure Ω'} (h' : IdentDistrib X X' μ μ') (hH : MeasurableSet (H : Set S)) :
    IsUniform H X' μ' := by sorry
