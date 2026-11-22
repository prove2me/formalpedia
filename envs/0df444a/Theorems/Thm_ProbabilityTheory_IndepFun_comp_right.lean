-- Prove2me | Theorems.Thm_ProbabilityTheory_IndepFun_comp_right
-- name    : ProbabilityTheory.IndepFun.comp_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:43.636377+00:00
-- url     : https://prove2.me/theorems/7ba42b8f-ae29-4694-bc4b-b6caa68ce425
-- title:
--   Indep Fun: comp right
-- statement:
--   Composing independent functions with a measurable embedding of conull range gives
--   independent
--   functions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L199-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L199-L216

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω
  → β} {g : Ω → β'}
variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
variable {f : Ω → α} {g : Ω → β}

theorem ProbabilityTheory.IndepFun.comp_right
    {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ,
  a ∈ range i)
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g μ) :
    IndepFun (f ∘ i) (g ∘ i) (μ.comap i) := by sorry
