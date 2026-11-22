-- Prove2me | Theorems.Thm_ProbabilityTheory_measureEntropy_eq_card_iff_measureReal_eq
-- name    : ProbabilityTheory.measureEntropy_eq_card_iff_measureReal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:37:00.516806+00:00
-- url     : https://prove2.me/theorems/6150b376-d88a-4d87-af18-aa9f35f22954
-- title:
--   Probability Theory: measure Entropy eq card iff measure Real eq
-- statement:
--   The Probability Theory construction uses the measure Entropy eq card iff measure Real eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean#L412-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean#L412-L421

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

theorem ProbabilityTheory.measureEntropy_eq_card_iff_measureReal_eq
    [Fintype S] [IsFiniteMeasure μ] [NeZero μ] :
    Hm[μ] = log (Fintype.card S) ↔ ∀ s : S,
      μ.real {s} = μ.real Set.univ / Fintype.card S := by sorry
