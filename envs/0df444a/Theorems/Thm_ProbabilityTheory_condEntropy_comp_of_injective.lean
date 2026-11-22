-- Prove2me | Theorems.Thm_ProbabilityTheory_condEntropy_comp_of_injective
-- name    : ProbabilityTheory.condEntropy_comp_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:56.882218+00:00
-- url     : https://prove2.me/theorems/2ff8f8e7-8fc4-4656-b774-f17ad1d82f9c
-- title:
--   Probability Theory: cond Entropy comp of injective
-- statement:
--   A weaker version of the above lemma in which `f` is independent of `Y`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L570-L573
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L570-L573

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
variable [Countable S]

theorem ProbabilityTheory.condEntropy_comp_of_injective {Y : Ω → U}
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Injective f) :
    H[f ∘ X | Y; μ] = H[X | Y; μ] := by sorry
