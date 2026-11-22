-- Prove2me | Theorems.Thm_ProbabilityTheory_entropy_add_entropy_sub_mutualInfo
-- name    : ProbabilityTheory.entropy_add_entropy_sub_mutualInfo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:09.798809+00:00
-- url     : https://prove2.me/theorems/d8aaf6c2-52e0-45f1-822b-bd3a9178bd95
-- title:
--   Probability Theory: entropy add entropy sub mutual Info
-- statement:
--   The Probability Theory construction uses the entropy add entropy sub mutual Info property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L738-L740
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L738-L740

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

theorem ProbabilityTheory.entropy_add_entropy_sub_mutualInfo
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    H[X; μ] + H[Y; μ] - I[X : Y; μ] = H[⟨X, Y⟩; μ] := by sorry
