-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
-- name    : ProbabilityTheory.Kernel.AEFiniteKernelSupport.snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:31:09.9553+00:00
-- url     : https://prove2.me/theorems/3c0d06df-d685-4830-8b43-e35ef50fe5e5
-- title:
--   AEFinite Kernel Support: snd
-- statement:
--   The AEFinite Kernel Support construction uses the snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L824-L830
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L824-L830

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

theorem ProbabilityTheory.Kernel.AEFiniteKernelSupport.snd
    [MeasurableSingletonClass U] {κ : Kernel T (S × U)} {μ :
  Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (snd κ) μ := by sorry
