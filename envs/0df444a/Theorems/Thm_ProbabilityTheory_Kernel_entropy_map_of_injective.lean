-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_map_of_injective
-- name    : ProbabilityTheory.Kernel.entropy_map_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:33:51.885217+00:00
-- url     : https://prove2.me/theorems/c107654f-a31f-45a2-a7c3-c6868d430484
-- title:
--   Kernel: entropy map of injective
-- statement:
--   The Kernel construction uses the entropy map of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L147-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L147-L151

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

theorem ProbabilityTheory.Kernel.entropy_map_of_injective [MeasurableSingletonClass U]
    (κ : Kernel T S) (μ : Measure T) {f : S
      → U} (hf : Function.Injective f) (hmes : Measurable f) :
    Hk[map κ f, μ] = Hk[κ, μ] := by sorry
