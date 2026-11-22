-- Prove2me | Theorems.Thm_ProbabilityTheory_entropy_of_uniformOn
-- name    : ProbabilityTheory.entropy_of_uniformOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:40:20.219784+00:00
-- url     : https://prove2.me/theorems/3e5e9963-ae35-4677-8410-03148505c82f
-- title:
--   Probability Theory: entropy of uniform On
-- statement:
--   The entropy of a uniform measure is the log of the cardinality of its support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean#L424-L442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean#L424-L442

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

theorem ProbabilityTheory.entropy_of_uniformOn (H : Set S) [Nonempty H] [Finite H] :
    measureEntropy (uniformOn H) = log (Nat.card H) := by sorry
