-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_nonempty_of_isProbabilityMeasure_of_isMarkovKernel
-- name    : ProbabilityTheory.Kernel.nonempty_of_isProbabilityMeasure_of_isMarkovKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:33:12.996502+00:00
-- url     : https://prove2.me/theorems/190fdcf1-378b-4ca0-a76e-7177d1352f98
-- title:
--   Kernel: nonempty of is Probability Measure of is Markov Kernel
-- statement:
--   The Kernel construction uses the nonempty of is Probability Measure of is Markov Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L339-L344
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L339-L344

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

theorem ProbabilityTheory.Kernel.nonempty_of_isProbabilityMeasure_of_isMarkovKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ :
      Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] : Nonempty β := by sorry
