-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_finiteKernelSupport_mk
-- name    : ProbabilityTheory.Kernel.AEFiniteKernelSupport.finiteKernelSupport_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:31:20.676105+00:00
-- url     : https://prove2.me/theorems/a2ddf403-f8af-4e81-b616-c35ca78eabae
-- title:
--   AEFinite Kernel Support: finite Kernel Support mk
-- statement:
--   The AEFinite Kernel Support construction uses the finite Kernel Support mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L646-L658
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L646-L658

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
variable [Countable T] [MeasurableSingletonClass T] {μ : Measure T}

theorem ProbabilityTheory.Kernel.AEFiniteKernelSupport.finiteKernelSupport_mk
    [MeasurableSingletonClass S] {κ : Kernel T S}
    (hκ : AEFiniteKernelSupport κ μ) :
    FiniteKernelSupport hκ.mk := by sorry
