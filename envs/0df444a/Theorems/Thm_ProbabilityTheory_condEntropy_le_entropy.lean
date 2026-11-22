-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_le_entropy
-- name    : ProbabilityTheory.condEntropy_le_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:59.687607+00:00
-- url     : https://prove2.me/theorems/ece282ae-54f5-42b8-8c7b-b5e07ea3b256
-- title:
--   Probability Theory: cond Entropy le entropy
-- statement:
--   `H[X | Y] ≤ H[X]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1177-L1180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1177-L1180

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
variable [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
variable [Countable U] [MeasurableSingletonClass U]
variable (μ)
variable [Countable S] [Countable T]
variable [IsZeroOrProbabilityMeasure μ]

theorem ProbabilityTheory.condEntropy_le_entropy
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : H[X | Y; μ] ≤ H[X; μ] := by sorry
