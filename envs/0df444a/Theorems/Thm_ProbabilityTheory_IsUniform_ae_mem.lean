-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_ae_mem
-- name    : ProbabilityTheory.IsUniform.ae_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:08.941259+00:00
-- url     : https://prove2.me/theorems/e981ff0e-3284-4ea4-a3c3-2453d093732a
-- title:
--   Is Uniform: ae mem
-- statement:
--   A uniform random variable on H almost surely takes values in H.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L122-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L122-L123

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

theorem ProbabilityTheory.IsUniform.ae_mem (h : IsUniform H X μ) : ∀ᵐ ω ∂μ,
  X ω ∈ H := by sorry
