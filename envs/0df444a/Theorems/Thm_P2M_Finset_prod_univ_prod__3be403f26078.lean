-- Prove2me | Theorems.Thm_P2M_Finset_prod_univ_prod__3be403f26078
-- name    : P2M_Finset_prod_univ_prod__3be403f26078
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:23:19.149676+00:00
-- url     : https://prove2.me/theorems/280214cc-f61c-49da-ae6d-02164643f745
-- title:
--   P2 M Finset prod univ prod  3be403f26078: P2 M Finset prod univ prod  3be403f26078
-- statement:
--   The P2 M Finset prod univ prod  3be403f26078 construction uses the P2 M Finset prod univ prod  3be403f26078 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L257-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L257-L259

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
variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i,
  κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}
variable [Fintype ι] [∀ i, Fintype (κ i)]

theorem P2M_Finset_prod_univ_prod__3be403f26078 {β : Type*} [CommMonoid β] (f : ((i : ι) × κ i) → β) :
    (∏ ij : (i : ι) × κ i, f ij) = (∏ i : ι, ∏ j : κ i, f ⟨i, j⟩) := by sorry

alias «Finset».«prod_univ_prod'» := P2M_Finset_prod_univ_prod__3be403f26078
