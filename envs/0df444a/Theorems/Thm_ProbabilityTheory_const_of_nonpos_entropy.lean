-- Prove2me | Theorems.Thm_ProbabilityTheory_const_of_nonpos_entropy
-- name    : ProbabilityTheory.const_of_nonpos_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:04:22.193635+00:00
-- url     : https://prove2.me/theorems/0285ae63-0866-4f45-9e43-accc6c4cecf3
-- title:
--   Probability Theory: const of nonpos entropy
-- statement:
--   If `X` is an `S`-valued random variable of non-positive entropy, then `X` is almost
--   surely
--   constant.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L340-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L340-L350

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

theorem ProbabilityTheory.const_of_nonpos_entropy [MeasurableSingletonClass S]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω
      → S} (hX : Measurable X) [FiniteRange X] (hent : H[X; μ] ≤ 0) :
    ∃ s : S, μ.real (X ⁻¹' {s}) = 1 := by sorry
