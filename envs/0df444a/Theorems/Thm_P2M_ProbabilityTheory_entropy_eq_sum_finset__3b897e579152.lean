-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_entropy_eq_sum_finset__3b897e579152
-- name    : P2M_ProbabilityTheory_entropy_eq_sum_finset__3b897e579152
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:09.576837+00:00
-- url     : https://prove2.me/theorems/bbdebae7-7b9c-470d-bd37-168be40a9474
-- title:
--   P2 M Probability Theory entropy eq sum finset  3b897e579152: P2 M Probability Theory entropy eq sum finset  3b897e579152
-- statement:
--   The P2 M Probability Theory entropy eq sum finset  3b897e579152 construction uses the P2 M Probability Theory entropy eq sum finset  3b897e579152 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L142-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L142-L145

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

theorem P2M_ProbabilityTheory_entropy_eq_sum_finset__3b897e579152 {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {A : Finset S} (hA : (μ.map X) Aᶜ = 0) :
    entropy X μ = ∑ x ∈ A, negMulLog ((μ.map X).real {x}) := by sorry

alias «ProbabilityTheory».«entropy_eq_sum_finset'» := P2M_ProbabilityTheory_entropy_eq_sum_finset__3b897e579152
