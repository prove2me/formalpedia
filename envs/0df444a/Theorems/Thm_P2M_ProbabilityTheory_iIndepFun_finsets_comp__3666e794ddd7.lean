-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_iIndepFun_finsets_comp__3666e794ddd7
-- name    : P2M_ProbabilityTheory_iIndepFun_finsets_comp__3666e794ddd7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:34.611132+00:00
-- url     : https://prove2.me/theorems/536552bb-41f2-4a0a-87b5-162163535d65
-- title:
--   P2 M Probability Theory i Indep Fun finsets comp  3666e794ddd7: P2 M Probability Theory i Indep Fun finsets comp  3666e794ddd7
-- statement:
--   A variant of iIndepFun.finsets_comp where we conclude the independence of just two
--   functions
--   rather than an entire family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L135-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L135-L163

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
variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  [n : ∀ i, MeasurableSpace (α i)]
  [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → α i}
  {μ : Measure Ω}
universe u

theorem P2M_ProbabilityTheory_iIndepFun_finsets_comp__3666e794ddd7 {f : ∀ i,
  Ω → β i} {S S' : Finset ι} (h_disjoint : Disjoint S S')
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    {γ γ' : Type u} {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'}
    {φ : (∀ i : S, β i) → γ} {φ' : (∀ i : S',
      β i) → γ'} (hφ : Measurable φ) (hφ' : Measurable φ') :
    IndepFun (fun a ↦ φ (fun (i : S) ↦ f i a)) (fun a ↦ φ' (fun (i : S') ↦ f i a)) μ := by sorry

alias «ProbabilityTheory».«iIndepFun».«finsets_comp'» := P2M_ProbabilityTheory_iIndepFun_finsets_comp__3666e794ddd7
