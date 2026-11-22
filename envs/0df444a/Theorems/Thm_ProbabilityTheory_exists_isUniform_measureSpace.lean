-- Prove2me | Theorems.Thm_ProbabilityTheory_exists_isUniform_measureSpace
-- name    : ProbabilityTheory.exists_isUniform_measureSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:19.394983+00:00
-- url     : https://prove2.me/theorems/7f4f75d3-c022-4faf-adbd-ad4260a69fa3
-- title:
--   Probability Theory: exists is Uniform measure Space
-- statement:
--   Uniform distributions exist, version giving a measure space
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L97-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L97-L104

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

theorem ProbabilityTheory.exists_isUniform_measureSpace {S : Type uS} [MeasurableSpace S]
    [MeasurableSingletonClass S] (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type uS) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U ∧ (∀ ω : Ω,
      U ω ∈ H) ∧
      FiniteRange U := by sorry
