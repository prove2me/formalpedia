-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_IsUniform_measureReal_preimage_of_mem__8a5ba6eaf935
-- name    : P2M_ProbabilityTheory_IsUniform_measureReal_preimage_of_mem__8a5ba6eaf935
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:29.41622+00:00
-- url     : https://prove2.me/theorems/a9a996fd-ea02-44d7-b3e9-fc341031fb76
-- title:
--   P2 M Probability Theory Is Uniform measure Real preimage of mem  8a5ba6eaf935: P2 M Probability Theory Is Uniform measure Real preimage of mem  8a5ba6eaf935
-- statement:
--   The P2 M Probability Theory Is Uniform measure Real preimage of mem  8a5ba6eaf935 construction uses the P2 M Probability Theory Is Uniform measure Real preimage of mem  8a5ba6eaf935 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L184-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L184-L188

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem P2M_ProbabilityTheory_IsUniform_measureReal_preimage_of_mem__8a5ba6eaf935
    {A : Finset S} [IsProbabilityMeasure μ]
    (h : IsUniform A X μ) (hX : Measurable X) {s : S} (hs : s ∈ A) :
    (μ.map X).real {s} = 1 / A.card := by sorry

alias «ProbabilityTheory».«IsUniform».«measureReal_preimage_of_mem'» := P2M_ProbabilityTheory_IsUniform_measureReal_preimage_of_mem__8a5ba6eaf935
