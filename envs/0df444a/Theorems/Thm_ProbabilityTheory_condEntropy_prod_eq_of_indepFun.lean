-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_prod_eq_of_indepFun
-- name    : ProbabilityTheory.condEntropy_prod_eq_of_indepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:57.108812+00:00
-- url     : https://prove2.me/theorems/5b27288a-ad81-45d3-8271-e3d29850c636
-- title:
--   Probability Theory: cond Entropy prod eq of indep Fun
-- statement:
--   The Probability Theory construction uses the cond Entropy prod eq of indep Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1104-L1123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1104-L1123

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

theorem ProbabilityTheory.condEntropy_prod_eq_of_indepFun
    [Finite T] [Finite U] [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X]
    (h : IndepFun (⟨X, Y⟩) Z μ) :
    H[X | ⟨Y, Z⟩; μ] = H[X | Y; μ] := by sorry
