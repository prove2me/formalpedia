-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_eq_sum_sum_fintype
-- name    : ProbabilityTheory.condEntropy_eq_sum_sum_fintype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:04:58.433614+00:00
-- url     : https://prove2.me/theorems/6bdd1086-2481-4d1a-b1f5-f76ed0e34320
-- title:
--   Probability Theory: cond Entropy eq sum sum fintype
-- statement:
--   `H[X|Y] = ∑_y ∑_x P[Y=y] P[X=x|Y=y] log ⧸(P[X=x|Y=y])`$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L528-L534
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L528-L534

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
variable [MeasurableSingletonClass T]
variable [MeasurableSingletonClass S]
omit [MeasurableSingletonClass S]

theorem ProbabilityTheory.condEntropy_eq_sum_sum_fintype {Y : Ω → T} (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype S] [Fintype T] :
    H[X | Y; μ] = ∑ y, ∑ x,
      (μ.map Y).real {y} * negMulLog (((μ[|Y ← y]).map X).real {x}) := by sorry
