-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_aefiniteKernelSupport_iff
-- name    : ProbabilityTheory.Kernel.aefiniteKernelSupport_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:33:16.834918+00:00
-- url     : https://prove2.me/theorems/eb27e49f-3af4-4683-b97c-bf9b2ad056c9
-- title:
--   Kernel: aefinite Kernel Support iff
-- statement:
--   The Kernel construction uses the aefinite Kernel Support iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L696-L703
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L696-L703

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

theorem ProbabilityTheory.Kernel.aefiniteKernelSupport_iff [MeasurableSingletonClass S] {κ : Kernel T S} {μ : Measure T} :
    AEFiniteKernelSupport κ μ ↔ ∃ κ' : Kernel T S,
      FiniteKernelSupport κ' ∧ κ' =ᵐ[μ] κ := by sorry
