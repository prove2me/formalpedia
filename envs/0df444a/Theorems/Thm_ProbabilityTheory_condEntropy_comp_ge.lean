-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_comp_ge
-- name    : ProbabilityTheory.condEntropy_comp_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:14.454174+00:00
-- url     : https://prove2.me/theorems/924df757-2324-4698-8957-742d4fe332c9
-- title:
--   Probability Theory: cond Entropy comp ge
-- statement:
--   Data-processing inequality for the conditional entropy: `H[Y|f(X)] ≥ H[Y|X]`
--   To upgrade this to equality, see `condEntropy_of_injective'`
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1199-L1212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1199-L1212

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

theorem ProbabilityTheory.condEntropy_comp_ge
    [FiniteRange X] [FiniteRange Y] (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (f : S
      → U) : H[Y | f ∘ X; μ] ≥ H[Y | X; μ] := by sorry
