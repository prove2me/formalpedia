-- Prove2me | Theorems.Thm_ProbabilityTheory_entropy_cond_eq_sum
-- name    : ProbabilityTheory.entropy_cond_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:04.579863+00:00
-- url     : https://prove2.me/theorems/c8523c02-1bb9-4e68-a95c-1ca1aeda2ba8
-- title:
--   Probability Theory: entropy cond eq sum
-- statement:
--   `H[X | Y=y] = ∑_s P[X=s | Y=y] log 1/(P[X=s | Y=y])`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L158-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L158-L163

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

theorem ProbabilityTheory.entropy_cond_eq_sum (μ : Measure Ω) (y : T) :
    H[X | Y ← y; μ] = ∑' x, negMulLog (((μ[|Y ← y]).map X).real {x}) := by sorry
