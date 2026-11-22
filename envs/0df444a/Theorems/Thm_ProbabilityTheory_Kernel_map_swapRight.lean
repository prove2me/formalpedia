-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_map_swapRight
-- name    : ProbabilityTheory.Kernel.map_swapRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:39:35.762896+00:00
-- url     : https://prove2.me/theorems/f093104d-877d-48d7-bfc1-219cdcf7d279
-- title:
--   Kernel: map swap Right
-- statement:
--   The Kernel construction uses the map swap Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Composition/Comp.lean#L39-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Composition/Comp.lean#L39-L46

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

theorem ProbabilityTheory.Kernel.map_swapRight (κ : Kernel α (β × γ)) {f : (γ × β) → δ} :
    map (swapRight κ) f = map κ (f ∘ Prod.swap) := by sorry
