-- Prove2me | Theorems.Thm_ProbabilityTheory_IdentDistrib_condEntropy_eq
-- name    : ProbabilityTheory.IdentDistrib.condEntropy_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:04.115708+00:00
-- url     : https://prove2.me/theorems/e96d6cf9-84b5-4fcc-8679-fa4dc80ee0c1
-- title:
--   Ident Distrib: cond Entropy eq
-- statement:
--   Two pairs of variables that have the same joint distribution, have the same
--   conditional entropy.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L633-L643
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L633-L643

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
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]

theorem ProbabilityTheory.IdentDistrib.condEntropy_eq
    {Ω' : Type*} [MeasurableSpace Ω'] {X : Ω → S} {Y : Ω → T}
    {μ' : Measure Ω'} {X' : Ω' → S} {Y' : Ω'
      → T} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (h : IdentDistrib (⟨X, Y⟩) (⟨X',
      Y'⟩) μ μ') [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    [FiniteRange Y'] :
    H[X | Y; μ] = H[X' | Y'; μ'] := by sorry
