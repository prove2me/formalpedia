-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_prodMkLeft
-- name    : ProbabilityTheory.Kernel.AEFiniteKernelSupport.prodMkLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:32:11.351222+00:00
-- url     : https://prove2.me/theorems/314562f4-2c0e-4fb8-a6f8-65a15c4cc88d
-- title:
--   AEFinite Kernel Support: prod Mk Left
-- statement:
--   The AEFinite Kernel Support construction uses the prod Mk Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L967-L982
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L967-L982

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

theorem ProbabilityTheory.Kernel.AEFiniteKernelSupport.prodMkLeft
    [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] [Countable U] {μ}
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ)
    (ν : Measure U) [SFinite μ] :
    AEFiniteKernelSupport (prodMkLeft U κ) (ν.prod μ) := by sorry
