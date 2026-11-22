-- Prove2me | Theorems.Thm_ProbabilityTheory_indepFun_fst_snd
-- name    : ProbabilityTheory.indepFun_fst_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:23:52.124528+00:00
-- url     : https://prove2.me/theorems/7c227373-a27b-4af5-bb46-1ab771bfb995
-- title:
--   Probability Theory: indep Fun fst snd
-- statement:
--   The Probability Theory construction uses the indep Fun fst snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L183-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L183-L192

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω
  → β} {g : Ω → β'}
variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]

theorem ProbabilityTheory.indepFun_fst_snd
    [IsZeroOrProbabilityMeasure μ] {μ'} [IsZeroOrProbabilityMeasure μ'] :
    IndepFun (Prod.fst : Ω × Ω' → Ω) (Prod.snd : Ω × Ω' → Ω') (μ.prod μ') := by sorry
