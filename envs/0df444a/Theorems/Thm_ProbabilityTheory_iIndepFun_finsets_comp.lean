-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_finsets_comp
-- name    : ProbabilityTheory.iIndepFun.finsets_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:29.090032+00:00
-- url     : https://prove2.me/theorems/c9ceb62c-124f-4558-aeb8-8a76232a1dc1
-- title:
--   i Indep Fun: finsets comp
-- statement:
--   If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise
--   disjoint
--   finite index sets, and `φ j` is a function that maps the tuple formed by `f i` for `i ∈
--   S j` to a
--   measurable space `γ j`, then the family of random variables formed by `φ j (f i)_{i ∈ S
--   j}` and
--   indexed by `J` is iIndep.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L83-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L83-L90

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_Kernel_iIndepFun_finsets_comp

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

theorem ProbabilityTheory.iIndepFun.finsets_comp
    {f : ∀ i, Ω → β i} {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    {γ : J → Type*} {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) μ := by sorry
