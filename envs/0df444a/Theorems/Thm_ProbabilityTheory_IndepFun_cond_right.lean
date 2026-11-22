-- Prove2me | Theorems.Thm_ProbabilityTheory_IndepFun_cond_right
-- name    : ProbabilityTheory.IndepFun.cond_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:30:03.859022+00:00
-- url     : https://prove2.me/theorems/d6aa6575-dd73-47b9-a0ea-e5014c7562cb
-- title:
--   Indep Fun: cond right
-- statement:
--   If `A` is independent of `B`, then they remain independent when conditioning on an
--   event
--   of the form `B ∈ t` of positive probability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L74-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L74-L77

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

theorem ProbabilityTheory.IndepFun.cond_right (h : IndepFun A B μ) {t : Set β}
    (ht : MeasurableSet t) (hB : Measurable B) :
    IndepFun A B (μ[| B⁻¹' t]) := by sorry
