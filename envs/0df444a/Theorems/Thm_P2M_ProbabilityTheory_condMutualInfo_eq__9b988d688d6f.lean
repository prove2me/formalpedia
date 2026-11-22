-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_condMutualInfo_eq__9b988d688d6f
-- name    : P2M_ProbabilityTheory_condMutualInfo_eq__9b988d688d6f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:44.698797+00:00
-- url     : https://prove2.me/theorems/18f9fdc9-fb65-4ca1-8a0d-7c59c86ef45b
-- title:
--   P2 M Probability Theory cond Mutual Info eq  9b988d688d6f: P2 M Probability Theory cond Mutual Info eq  9b988d688d6f
-- statement:
--   `I[X : Y| Z] = H[X| Z] - H[X|Y, Z]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1037-L1043
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1037-L1043

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
variable [MeasurableSingletonClass U]

theorem P2M_ProbabilityTheory_condMutualInfo_eq__9b988d688d6f [Countable U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z; μ] = H[X | Z; μ] - H[X | ⟨Y, Z⟩; μ] := by sorry

alias «ProbabilityTheory».«condMutualInfo_eq'» := P2M_ProbabilityTheory_condMutualInfo_eq__9b988d688d6f
