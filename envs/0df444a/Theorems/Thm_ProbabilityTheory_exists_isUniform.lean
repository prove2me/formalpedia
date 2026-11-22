-- Prove2me | Theorems.Thm_ProbabilityTheory_exists_isUniform
-- name    : ProbabilityTheory.exists_isUniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:12.103807+00:00
-- url     : https://prove2.me/theorems/cd5db009-94d1-4785-8ec8-d358380bf8c7
-- title:
--   Probability Theory: exists is Uniform
-- statement:
--   Uniform distributions exist.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L54-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L54-L79

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

theorem ProbabilityTheory.exists_isUniform [MeasurableSpace S] [MeasurableSingletonClass S]
    (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type uS) (_ : MeasurableSpace Ω) (X : Ω → S) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧ Measurable X ∧ IsUniform H X μ ∧ (∀ ω,
        X ω ∈ H) ∧ FiniteRange X := by sorry
