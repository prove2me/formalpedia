-- Prove2me | Theorems.Thm_ProbabilityTheory_IndepFun_identDistrib_cond
-- name    : ProbabilityTheory.IndepFun.identDistrib_cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:27.601832+00:00
-- url     : https://prove2.me/theorems/44a93052-7d4a-428e-a93f-a5a1bc4a5eab
-- title:
--   Indep Fun: ident Distrib cond
-- statement:
--   If `A` is independent from `B`, then conditioning on an event given by `B` does not
--   change
--   the distribution of `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L38-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L38-L47

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

theorem ProbabilityTheory.IndepFun.identDistrib_cond [IsProbabilityMeasure μ]
    (hi : IndepFun A B μ) {s : Set β}
    (hs : MeasurableSet s) (hA : Measurable A) (hB : Measurable B)
    (h : μ (B ⁻¹' s) ≠ 0) :
    IdentDistrib A A μ (μ[|B ⁻¹' s]) := by sorry
