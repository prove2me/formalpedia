-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_map_swap
-- name    : ProbabilityTheory.Kernel.entropy_map_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:37:17.734228+00:00
-- url     : https://prove2.me/theorems/a76a1a1c-775f-47be-82e4-fe97bebe860d
-- title:
--   Kernel: entropy map swap
-- statement:
--   The Kernel construction uses the entropy map swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L153-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L153-L156

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

theorem ProbabilityTheory.Kernel.entropy_map_swap [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (κ : Kernel T (S × U)) (μ : Measure T) :
    Hk[map κ Prod.swap, μ] = Hk[κ, μ] := by sorry
