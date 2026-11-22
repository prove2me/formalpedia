-- Prove2me | Theorems.Thm_ProbabilityTheory_IndepFun_cond_left
-- name    : ProbabilityTheory.IndepFun.cond_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:28.16924+00:00
-- url     : https://prove2.me/theorems/652bd28c-080a-40b5-90dd-e9efffb98c41
-- title:
--   Indep Fun: cond left
-- statement:
--   If `A` is independent of `B`, then they remain independent when conditioning on an
--   event
--   of the form `A ∈ s` of positive probability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L52-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L52-L69

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
variable {Ω α β : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α} {_ :
  MeasurableSpace β}
  {μ : Measure Ω} {A : Ω → α} {B : Ω → β}

theorem ProbabilityTheory.IndepFun.cond_left (hi : IndepFun A B μ) {s : Set α}
    (hs : MeasurableSet s) (hA : Measurable A) :
    IndepFun A B (μ[| A⁻¹' s]) := by sorry
