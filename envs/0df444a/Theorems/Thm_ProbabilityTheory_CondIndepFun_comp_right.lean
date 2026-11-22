-- Prove2me | Theorems.Thm_ProbabilityTheory_CondIndepFun_comp_right
-- name    : ProbabilityTheory.CondIndepFun.comp_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:30:04.366832+00:00
-- url     : https://prove2.me/theorems/5a42aee2-bf62-47c3-905c-595092af280e
-- title:
--   Cond Indep Fun: comp right
-- statement:
--   Composing independent functions with a measurable embedding of conull range gives
--   independent
--   functions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L142-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L142-L150

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_comp_right
public import Theorems.Thm_ProbabilityTheory_IndepFun_comp_right

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Measure Set
open scoped ENNReal ZhangYeungPFR
open ProbabilityTheory
variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω
    → β} {h : Ω → γ}
variable [MeasurableSingletonClass γ]

theorem ProbabilityTheory.CondIndepFun.comp_right {i : Ω'
  → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hfg : CondIndepFun f g h μ) :
    CondIndepFun (f ∘ i) (g ∘ i) (h ∘ i) (μ.comap i) := by sorry
