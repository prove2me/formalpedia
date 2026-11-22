-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_entropy_eq
-- name    : ProbabilityTheory.IsUniform.entropy_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:26.43575+00:00
-- url     : https://prove2.me/theorems/5afc23a4-6910-478b-8b67-5c8eb4ec8832
-- title:
--   Is Uniform: entropy eq
-- statement:
--   If `X` is uniformly distributed on `H`, then `H[X] = log |H|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L198-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L198-L213

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

theorem ProbabilityTheory.IsUniform.entropy_eq
    [DiscreteMeasurableSpace S] {H : Finset S} {X : Ω
  → S} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsUniform H X μ) (hX' : Measurable X) :
    H[X; μ] = log (Nat.card H) := by sorry
