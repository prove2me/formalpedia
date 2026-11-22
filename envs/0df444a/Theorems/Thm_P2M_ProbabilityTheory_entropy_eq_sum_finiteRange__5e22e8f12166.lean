-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_entropy_eq_sum_finiteRange__5e22e8f12166
-- name    : P2M_ProbabilityTheory_entropy_eq_sum_finiteRange__5e22e8f12166
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:03:30.507363+00:00
-- url     : https://prove2.me/theorems/88fca7a5-a7fe-42a7-b548-06906099f6b9
-- title:
--   P2 M Probability Theory entropy eq sum finite Range  5e22e8f12166: P2 M Probability Theory entropy eq sum finite Range  5e22e8f12166
-- statement:
--   The P2 M Probability Theory entropy eq sum finite Range  5e22e8f12166 construction uses the P2 M Probability Theory entropy eq sum finite Range  5e22e8f12166 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L152-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L152-L155

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

theorem P2M_ProbabilityTheory_entropy_eq_sum_finiteRange__5e22e8f12166 [MeasurableSingletonClass S] (hX : Measurable X) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] :
    entropy X μ = ∑ x ∈ FiniteRange.toFinset X, negMulLog ((μ.map X).real {x}) := by sorry

alias «ProbabilityTheory».«entropy_eq_sum_finiteRange'» := P2M_ProbabilityTheory_entropy_eq_sum_finiteRange__5e22e8f12166
