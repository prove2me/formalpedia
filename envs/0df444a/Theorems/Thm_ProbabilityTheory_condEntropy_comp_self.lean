-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_comp_self
-- name    : ProbabilityTheory.condEntropy_comp_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:05:51.786882+00:00
-- url     : https://prove2.me/theorems/223f200e-a6a1-49e4-bbc0-29e4c665ec00
-- title:
--   Probability Theory: cond Entropy comp self
-- statement:
--   `H[X | f(X)] = H[X] - H[f(X)]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L661-L664
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L661-L664

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
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
variable [Countable U] [MeasurableSingletonClass U]

theorem ProbabilityTheory.condEntropy_comp_self
    [IsProbabilityMeasure μ] (hX : Measurable X) {f : S → U}
    (hf : Measurable f) [FiniteRange X] : H[X | f ∘ X; μ] = H[X; μ] - H[f ∘ X; μ] := by sorry
