-- Prove2me | Theorems.Thm_ProbabilityTheory_Measure_ext_iff_singleton_finiteSupport
-- name    : ProbabilityTheory.Measure.ext_iff_singleton_finiteSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:36:53.941809+00:00
-- url     : https://prove2.me/theorems/f0296995-a470-47b0-b579-ebe96d137a82
-- title:
--   Measure: ext iff singleton finite Support
-- statement:
--   This generalizes Measure.ext_iff_singleton ∈ MeasureReal
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean#L211-L237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean#L211-L237

module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Dirac
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal NNReal Topology
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U]
variable {μ : Measure S}
variable [MeasurableSingletonClass S]

theorem ProbabilityTheory.Measure.ext_iff_singleton_finiteSupport
    {μ1 μ2 : Measure S} [FiniteSupport μ1] [FiniteSupport μ2] :
    μ1 = μ2 ↔ ∀ x, μ1 {x} = μ2 {x} := by sorry
