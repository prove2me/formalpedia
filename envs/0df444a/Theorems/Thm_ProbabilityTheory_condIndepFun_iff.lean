-- Prove2me | Theorems.Thm_ProbabilityTheory_condIndepFun_iff
-- name    : ProbabilityTheory.condIndepFun_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:23:44.988953+00:00
-- url     : https://prove2.me/theorems/2357298f-1040-4ed4-b661-7047a84b22d5
-- title:
--   Probability Theory: cond Indep Fun iff
-- statement:
--   The Probability Theory construction uses the cond Indep Fun iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L134-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L134-L135

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Measure Set
open scoped ENNReal ZhangYeungPFR
open ProbabilityTheory
variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω
    → β} {h : Ω → γ}

theorem ProbabilityTheory.condIndepFun_iff : CondIndepFun f g h μ ↔ ∀ᵐ z ∂ (μ.map h),
  IndepFun f g (μ[|h ← z]) := by sorry
