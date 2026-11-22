-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_measureEntropy_of_isProbabilityMeasure__887b39d20cfb
-- name    : P2M_ProbabilityTheory_measureEntropy_of_isProbabilityMeasure__887b39d20cfb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:40:14.234374+00:00
-- url     : https://prove2.me/theorems/b380de9d-afc0-4fa1-971c-c56602664730
-- title:
--   P2 M Probability Theory measure Entropy of is Probability Measure  887b39d20cfb: P2 M Probability Theory measure Entropy of is Probability Measure  887b39d20cfb
-- statement:
--   The P2 M Probability Theory measure Entropy of is Probability Measure  887b39d20cfb construction uses the P2 M Probability Theory measure Entropy of is Probability Measure  887b39d20cfb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean#L287-L290
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean#L287-L290

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

theorem P2M_ProbabilityTheory_measureEntropy_of_isProbabilityMeasure__887b39d20cfb
    (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) := by sorry

alias «ProbabilityTheory».«measureEntropy_of_isProbabilityMeasure'» := P2M_ProbabilityTheory_measureEntropy_of_isProbabilityMeasure__887b39d20cfb
