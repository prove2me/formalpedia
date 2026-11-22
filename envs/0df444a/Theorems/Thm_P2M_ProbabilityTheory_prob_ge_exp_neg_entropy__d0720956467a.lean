-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_prob_ge_exp_neg_entropy__d0720956467a
-- name    : P2M_ProbabilityTheory_prob_ge_exp_neg_entropy__d0720956467a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:26.743415+00:00
-- url     : https://prove2.me/theorems/5b6de11e-c349-441c-951e-f771a5877dbe
-- title:
--   P2 M Probability Theory prob ge exp neg entropy  d0720956467a: P2 M Probability Theory prob ge exp neg entropy  d0720956467a
-- statement:
--   If `X` is an `S`-valued random variable, then there exists `s ∈ S` such that
--   `P[X=s] ≥ \exp(-H[X])`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L326-L335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L326-L335

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

theorem P2M_ProbabilityTheory_prob_ge_exp_neg_entropy__d0720956467a [MeasurableSingletonClass S]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X) [FiniteRange X] :
    ∃ s : S, rexp (- H[X; μ]) ≤ μ.real (X ⁻¹' {s}) := by sorry

alias «ProbabilityTheory».«prob_ge_exp_neg_entropy'» := P2M_ProbabilityTheory_prob_ge_exp_neg_entropy__d0720956467a
