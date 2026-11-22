-- Prove2me | Theorems.Thm_ProbabilityTheory_IdentDistrib_of_isUniform
-- name    : ProbabilityTheory.IdentDistrib.of_isUniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:36.17682+00:00
-- url     : https://prove2.me/theorems/ede4c6db-3250-4289-86ad-94d083d7cc45
-- title:
--   Ident Distrib: of is Uniform
-- statement:
--   The Ident Distrib construction uses the of is Uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L279-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L279-L299

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

theorem ProbabilityTheory.IdentDistrib.of_isUniform
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Finite H] [Countable S]
    {X : Ω → S} {X' : Ω' → S}
    (hX : Measurable X) (hX' : Measurable X') (hX_unif : IsUniform H X μ)
    (hX'_unif : IsUniform H X' μ') : IdentDistrib X X' μ μ' := by sorry
