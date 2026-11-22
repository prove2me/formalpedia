-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_map_eq_uniformOn
-- name    : ProbabilityTheory.IsUniform.map_eq_uniformOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:06.508797+00:00
-- url     : https://prove2.me/theorems/d3a4e7d9-8481-4c0f-81a2-a11dd5319cc1
-- title:
--   Is Uniform: map eq uniform On
-- statement:
--   The Is Uniform construction uses the map eq uniform On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L301-L308
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L301-L308

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

theorem ProbabilityTheory.IsUniform.map_eq_uniformOn [Countable S] [IsProbabilityMeasure μ]
    {H : Set S} (h : IsUniform H X μ) (hX : Measurable X) (hH : H.Finite) (h'H : H.Nonempty) :
    μ.map X = uniformOn H := by sorry
