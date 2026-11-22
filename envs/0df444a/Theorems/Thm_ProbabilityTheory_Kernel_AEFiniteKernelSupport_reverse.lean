-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_reverse
-- name    : ProbabilityTheory.Kernel.AEFiniteKernelSupport.reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:33:32.128998+00:00
-- url     : https://prove2.me/theorems/99fac700-0c15-425e-a8a5-4ac06bc91ece
-- title:
--   AEFinite Kernel Support: reverse
-- statement:
--   The AEFinite Kernel Support construction uses the reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Composition/Comp.lean#L221-L227
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Composition/Comp.lean#L221-L227

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
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

theorem ProbabilityTheory.Kernel.AEFiniteKernelSupport.reverse
    [MeasurableSingletonClass S] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {κ : Kernel T (S × β × γ)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (reverse κ) μ := by sorry
