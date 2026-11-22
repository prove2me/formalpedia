-- Prove2me | Theorems.Thm_ProbabilityTheory_prob_ge_exp_neg_entropy
-- name    : ProbabilityTheory.prob_ge_exp_neg_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:29.633632+00:00
-- url     : https://prove2.me/theorems/ea3b6d31-242c-4757-9ee6-67414215b820
-- title:
--   Probability Theory: prob ge exp neg entropy
-- statement:
--   If `X` is an `S`-valued random variable, then there exists `s ∈ S` such that
--   `P[X = s] ≥ \exp(- H[X])`.
--
--   TODO: remove the probability measure hypothesis, which is unnecessary here.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L243-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L243-L322

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
open Set
open Function

theorem ProbabilityTheory.prob_ge_exp_neg_entropy [MeasurableSingletonClass S] (X : Ω → S) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : Measurable X) [hX' : FiniteRange X] :
    ∃ s : S, μ Set.univ * (rexp (- H[X; μ])).toNNReal ≤ μ.map X {s} := by sorry
