-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_measureReal_preimage_of_nmem
-- name    : ProbabilityTheory.IsUniform.measureReal_preimage_of_nmem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:23.860795+00:00
-- url     : https://prove2.me/theorems/5398b235-7967-4e93-9820-e188cc5ebb1f
-- title:
--   Is Uniform: measure Real preimage of nmem
-- statement:
--   Another "unit test" for the definition of uniform distribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L141-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L141-L144

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

theorem ProbabilityTheory.IsUniform.measureReal_preimage_of_nmem
    (h : IsUniform H X μ) {s : S} (hs : s ∉ H) :
    μ.real (X ⁻¹' {s}) = 0 := by sorry
