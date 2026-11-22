-- Prove2me | Theorems.Thm_ProbabilityTheory_condMutualInfo_eq_sum
-- name    : ProbabilityTheory.condMutualInfo_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:16.073884+00:00
-- url     : https://prove2.me/theorems/d9e68b88-3459-4ec4-a209-51ddfb1036df
-- title:
--   Probability Theory: cond Mutual Info eq sum
-- statement:
--   The Probability Theory construction uses the cond Mutual Info eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L973-L983
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L973-L983

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

theorem ProbabilityTheory.condMutualInfo_eq_sum
    [MeasurableSingletonClass U] [IsFiniteMeasure μ]
    (hZ : Measurable Z) [FiniteRange Z] :
    I[X : Y | Z; μ] = ∑ z ∈ FiniteRange.toFinset Z,
      μ.real (Z ⁻¹' {z}) * I[X : Y; μ[|Z ← z]] := by sorry
