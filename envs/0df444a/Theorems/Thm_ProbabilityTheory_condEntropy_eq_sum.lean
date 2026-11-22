-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_eq_sum
-- name    : ProbabilityTheory.condEntropy_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:48.008527+00:00
-- url     : https://prove2.me/theorems/b427b3d3-20ee-4d39-89b4-0c9609067b46
-- title:
--   Probability Theory: cond Entropy eq sum
-- statement:
--   `H[X|Y] = ∑_y P[Y=y] H[X|Y=y]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L471-L479
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L471-L479

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

theorem ProbabilityTheory.condEntropy_eq_sum
    [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω
  → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] (hY : Measurable Y) [FiniteRange Y] :
    H[X | Y; μ] = ∑ y ∈ FiniteRange.toFinset Y,
      ((μ.map Y).real {y}) * H[X | Y ← y; μ] := by sorry
