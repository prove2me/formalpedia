-- Prove2me | Theorems.Thm_ProbabilityTheory_entropy_eq_sum_finset
-- name    : ProbabilityTheory.entropy_eq_sum_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:52:19.287959+00:00
-- url     : https://prove2.me/theorems/f75bd2fd-0d6e-4b16-a8ca-0a0dbd9ceb1c
-- title:
--   Probability Theory: entropy eq sum finset
-- statement:
--   The Probability Theory construction uses the entropy eq sum finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L129-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L129-L140

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

theorem ProbabilityTheory.entropy_eq_sum_finset {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {A : Finset S} (hA : (μ.map X) Aᶜ = 0) :
    entropy X μ = ∑ x ∈ A, negMulLog ((μ.map X).real {x}) := by sorry
