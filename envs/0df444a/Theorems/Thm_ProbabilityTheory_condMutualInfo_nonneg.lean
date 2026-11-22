-- Prove2me | Theorems.Thm_ProbabilityTheory_condMutualInfo_nonneg
-- name    : ProbabilityTheory.condMutualInfo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:51:37.349091+00:00
-- url     : https://prove2.me/theorems/20632fdb-b4d3-4ef7-ab1f-e1492493b4a2
-- title:
--   Probability Theory: cond Mutual Info nonneg
-- statement:
--   Conditional information is non-nonegative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1004-L1009
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1004-L1009

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

theorem ProbabilityTheory.condMutualInfo_nonneg
    (hX : Measurable X) (hY : Measurable Y) {Z : Ω → U} {μ : Measure Ω}
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ I[X : Y | Z; μ] := by sorry
