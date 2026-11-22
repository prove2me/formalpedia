-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
-- name    : ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:32:41.178092+00:00
-- url     : https://prove2.me/theorems/aa4575be-d634-4bcd-a63c-6bf5f618474c
-- title:
--   Kernel: swap Right delete Middle reverse
-- statement:
--   The Kernel construction uses the swap Right delete Middle reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Composition/Comp.lean#L193-L197
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Composition/Comp.lean#L193-L197

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_swapRight

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {α β γ δ ε : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {_ : MeasurableSpace ε}
variable {Ω S T : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace γ]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → β}

theorem ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteMiddle (reverse κ)) = deleteMiddle κ := by sorry
