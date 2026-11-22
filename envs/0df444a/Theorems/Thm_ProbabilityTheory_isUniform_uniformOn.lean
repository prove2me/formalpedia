-- Prove2me | Theorems.Thm_ProbabilityTheory_isUniform_uniformOn
-- name    : ProbabilityTheory.isUniform_uniformOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:15.878542+00:00
-- url     : https://prove2.me/theorems/2f7c620d-19d1-4dd4-bd0f-d9940acc3117
-- title:
--   Probability Theory: is Uniform uniform On
-- statement:
--   The Probability Theory construction uses the is Uniform uniform On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L44-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L44-L51

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

theorem ProbabilityTheory.isUniform_uniformOn [MeasurableSingletonClass Ω] {A : Set Ω} :
    IsUniform A id (uniformOn A) := by sorry
