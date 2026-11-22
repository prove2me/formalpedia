-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_eq_sum_fintype
-- name    : ProbabilityTheory.condEntropy_eq_sum_fintype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:59.748802+00:00
-- url     : https://prove2.me/theorems/f89a313b-70e7-4f5c-8c93-dfce8ad9973e
-- title:
--   Probability Theory: cond Entropy eq sum fintype
-- statement:
--   `H[X|Y] = ∑_y P[Y=y] H[X|Y=y]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L482-L487
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L482-L487

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
variable {X : Ω → S} {Y : Ω → T}

theorem ProbabilityTheory.condEntropy_eq_sum_fintype
    [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] (hY : Measurable Y) [Fintype T] :
    H[X | Y; μ] = ∑ y, μ.real (Y ⁻¹' {y}) * H[X | Y ← y; μ] := by sorry
