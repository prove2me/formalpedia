-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_exists_isUniform_measureSpace__68d4ee0dc9af
-- name    : P2M_ProbabilityTheory_exists_isUniform_measureSpace__68d4ee0dc9af
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:12.486654+00:00
-- url     : https://prove2.me/theorems/7ea83148-9256-4855-b380-3a1fcd6aef96
-- title:
--   P2 M Probability Theory exists is Uniform measure Space  68d4ee0dc9af: P2 M Probability Theory exists is Uniform measure Space  68d4ee0dc9af
-- statement:
--   Uniform distributions exist, version with a Finite set rather than a Finset and
--   giving a
--   measure
--   space
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L110-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L110-L119

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

theorem P2M_ProbabilityTheory_exists_isUniform_measureSpace__68d4ee0dc9af {S : Type uS} [MeasurableSpace S]
    [MeasurableSingletonClass S] (H : Set S) (hH : H.Finite) (h'H : H.Nonempty) :
    ∃ (Ω : Type uS) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U
      ∧ (∀ ω, U ω ∈ H) ∧ FiniteRange U := by sorry

alias «ProbabilityTheory».«exists_isUniform_measureSpace'» := P2M_ProbabilityTheory_exists_isUniform_measureSpace__68d4ee0dc9af
