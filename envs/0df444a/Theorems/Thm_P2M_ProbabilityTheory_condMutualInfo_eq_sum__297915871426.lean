-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_condMutualInfo_eq_sum__297915871426
-- name    : P2M_ProbabilityTheory_condMutualInfo_eq_sum__297915871426
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:30.469141+00:00
-- url     : https://prove2.me/theorems/b65b2ad1-e0d0-4c45-bfd2-956767432ac0
-- title:
--   P2 M Probability Theory cond Mutual Info eq sum  297915871426: P2 M Probability Theory cond Mutual Info eq sum  297915871426
-- statement:
--   A variant of `condMutualInfo_eq_sum` when `Z` has finite codomain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L986-L997
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L986-L997

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

theorem P2M_ProbabilityTheory_condMutualInfo_eq_sum__297915871426
    [MeasurableSingletonClass U] [IsFiniteMeasure μ]
    (hZ : Measurable Z) [Fintype U] :
    I[X : Y | Z; μ] = ∑ z, μ.real (Z ⁻¹' {z}) * I[X : Y; (μ[|Z ← z])] := by sorry

alias «ProbabilityTheory».«condMutualInfo_eq_sum'» := P2M_ProbabilityTheory_condMutualInfo_eq_sum__297915871426
