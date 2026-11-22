-- Prove2me | Theorems.Thm_ProbabilityTheory_IndepFun_cond
-- name    : ProbabilityTheory.IndepFun.cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:30:28.54495+00:00
-- url     : https://prove2.me/theorems/0d5f2276-2611-40bf-895f-f83bf67bbc9b
-- title:
--   Indep Fun: cond
-- statement:
--   If `A` is independent of `B`, then they remain independent when conditioning on an
--   event
--   of the form `A ∈ s ∩ B ∈ t` of positive probability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L82-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L82-L119

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_cond

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Measure Set
open scoped ENNReal ZhangYeungPFR
open ProbabilityTheory
variable {Ω α β : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α} {_ :
  MeasurableSpace β}
  {μ : Measure Ω} {A : Ω → α} {B : Ω → β}

theorem ProbabilityTheory.IndepFun.cond (hi : IndepFun A B μ) {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hA : Measurable A) (hB : Measurable B) :
    IndepFun A B (μ[| A ⁻¹' s ∩ B ⁻¹' t]) := by sorry
