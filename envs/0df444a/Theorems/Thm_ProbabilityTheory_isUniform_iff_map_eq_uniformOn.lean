-- Prove2me | Theorems.Thm_ProbabilityTheory_isUniform_iff_map_eq_uniformOn
-- name    : ProbabilityTheory.isUniform_iff_map_eq_uniformOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:21.72084+00:00
-- url     : https://prove2.me/theorems/daf2fb72-04e8-4cca-8a5c-4a1a2569a079
-- title:
--   Probability Theory: is Uniform iff map eq uniform On
-- statement:
--   A random variable is uniform iff its distribution is.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L311-L349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L311-L349

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

theorem ProbabilityTheory.isUniform_iff_map_eq_uniformOn [Finite H] {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ :
  Measure Ω)
    [Countable S] [IsProbabilityMeasure μ] {U : Ω → S} (hU : Measurable U) :
    IsUniform H U μ ↔ μ.map U = uniformOn H := by sorry
