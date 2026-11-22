-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_condEntropy_of_injective__9847cc7a9a3e
-- name    : P2M_ProbabilityTheory_condEntropy_of_injective__9847cc7a9a3e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:41.66892+00:00
-- url     : https://prove2.me/theorems/356e74e5-afc1-42ab-bd69-4696eb37a6ae
-- title:
--   P2 M Probability Theory cond Entropy of injective  9847cc7a9a3e: P2 M Probability Theory cond Entropy of injective  9847cc7a9a3e
-- statement:
--   If `X : Ω → S` and `Y : Ω → T` are random variables, and `f : T → U` is an
--   injection then `H[X | f(Y)] = H[X | Y]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L649-L658
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L649-L658

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

theorem P2M_ProbabilityTheory_condEntropy_of_injective__9847cc7a9a3e (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (f : T → U)
    (hf : Injective f)
    (hfY : Measurable (f ∘ Y)) [FiniteRange X] [FiniteRange Y] :
    H[X | f ∘ Y; μ] = H[X | Y; μ] := by sorry

alias «ProbabilityTheory».«condEntropy_of_injective'» := P2M_ProbabilityTheory_condEntropy_of_injective__9847cc7a9a3e
