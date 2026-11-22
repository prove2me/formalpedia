-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_IsUniform_entropy_eq__82cd2662f744
-- name    : P2M_ProbabilityTheory_IsUniform_entropy_eq__82cd2662f744
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:04:02.941942+00:00
-- url     : https://prove2.me/theorems/d95582b7-4700-4bfb-8039-8a697316c240
-- title:
--   P2 M Probability Theory Is Uniform entropy eq  82cd2662f744: P2 M Probability Theory Is Uniform entropy eq  82cd2662f744
-- statement:
--   Variant of `IsUniform.entropy_congr` where `H` is a finite `Set` rather than `Finset`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L218-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L218-L222

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
open Set
open Function

theorem P2M_ProbabilityTheory_IsUniform_entropy_eq__82cd2662f744 [DiscreteMeasurableSpace S]
    {A : Set S} (hA : A.Finite) {X : Ω → S} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsUniform A X μ) (hX' : Measurable X) : H[X; μ] = log A.ncard := by sorry

alias «ProbabilityTheory».«IsUniform».«entropy_eq'» := P2M_ProbabilityTheory_IsUniform_entropy_eq__82cd2662f744
