-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_eq_sum_prod
-- name    : ProbabilityTheory.condEntropy_eq_sum_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:04:59.957476+00:00
-- url     : https://prove2.me/theorems/e8a5627b-ebea-459e-8b82-14dc6f0d9255
-- title:
--   Probability Theory: cond Entropy eq sum prod
-- statement:
--   Same as previous lemma, but with a sum over a product space rather than a double sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L539-L544
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L539-L544

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

theorem ProbabilityTheory.condEntropy_eq_sum_prod (hX : Measurable X) {Y : Ω → T}
    (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[X | Y; μ] = ∑ p ∈ (FiniteRange.toFinset X) ×ˢ (FiniteRange.toFinset Y),
      (μ.map Y).real {p.2} * negMulLog (((μ[|Y ⁻¹' {p.2}]).map X).real {p.1}) := by sorry
