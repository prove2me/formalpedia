-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_entropy_sub_mutualInfo_eq_condEntropy__e9f8ff5b3eed
-- name    : P2M_ProbabilityTheory_entropy_sub_mutualInfo_eq_condEntropy__e9f8ff5b3eed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:16.408797+00:00
-- url     : https://prove2.me/theorems/61c54578-7c6f-4ae5-ad07-f7ee8d61c04c
-- title:
--   P2 M Probability Theory entropy sub mutual Info eq cond Entropy  e9f8ff5b3eed: P2 M Probability Theory entropy sub mutual Info eq cond Entropy  e9f8ff5b3eed
-- statement:
--   `H[Y] - I[X : Y] = H[Y | X]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L922-L927
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L922-L927

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
variable [Countable S] [Countable T]

theorem P2M_ProbabilityTheory_entropy_sub_mutualInfo_eq_condEntropy__e9f8ff5b3eed
    (hX : Measurable X) (hY : Measurable Y) (μ :
  Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[Y; μ] - I[X : Y; μ] = H[Y | X; μ] := by sorry

alias «ProbabilityTheory».«entropy_sub_mutualInfo_eq_condEntropy'» := P2M_ProbabilityTheory_entropy_sub_mutualInfo_eq_condEntropy__e9f8ff5b3eed
