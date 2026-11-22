-- Prove2me | Theorems.Thm_ProbabilityTheory_entropy_cond_eq_sum_finiteRange
-- name    : ProbabilityTheory.entropy_cond_eq_sum_finiteRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:20.671155+00:00
-- url     : https://prove2.me/theorems/5e815345-8f75-428d-a549-c1efdb8c36df
-- title:
--   Probability Theory: entropy cond eq sum finite Range
-- statement:
--   The Probability Theory construction uses the entropy cond eq sum finite Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L165-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L165-L172

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

theorem ProbabilityTheory.entropy_cond_eq_sum_finiteRange [MeasurableSingletonClass S]
    (hX : Measurable X) (μ : Measure Ω) (y : T) [FiniteRange X] :
    H[X | Y ← y; μ] = ∑ x ∈ FiniteRange.toFinset X,
      negMulLog (((μ[|Y ← y]).map X).real {x}) := by sorry
