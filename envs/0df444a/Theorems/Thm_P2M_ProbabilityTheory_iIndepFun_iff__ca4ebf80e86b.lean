-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_iIndepFun_iff__ca4ebf80e86b
-- name    : P2M_ProbabilityTheory_iIndepFun_iff__ca4ebf80e86b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:28:08.395327+00:00
-- url     : https://prove2.me/theorems/f6d58a80-01d5-4928-a394-db7582237b1f
-- title:
--   P2 M Probability Theory i Indep Fun iff  ca4ebf80e86b: P2 M Probability Theory i Indep Fun iff  ca4ebf80e86b
-- statement:
--   The P2 M Probability Theory i Indep Fun iff  ca4ebf80e86b construction uses the P2 M Probability Theory i Indep Fun iff  ca4ebf80e86b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L220-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L220-L234

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

theorem P2M_ProbabilityTheory_iIndepFun_iff__ca4ebf80e86b [MeasurableSpace Ω] {β : ι → Type*}
    (m : ∀ i, MeasurableSpace (β i)) (f : ∀ i, Ω → β i) (μ : Measure Ω) :
    iIndepFun f μ ↔ ∀ (s : Finset ι) ⦃f' : ι → Set Ω⦄
      (_hf' : ∀ i, MeasurableSet[(m i).comap (f i)] (f' i)),
      μ (⋂ i ∈ s, f' i) = ∏ i ∈ s, μ (f' i) := by sorry

alias «ProbabilityTheory».«iIndepFun_iff'» := P2M_ProbabilityTheory_iIndepFun_iff__ca4ebf80e86b
