-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_finsets
-- name    : ProbabilityTheory.iIndepFun.finsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:54.905196+00:00
-- url     : https://prove2.me/theorems/06a58a8c-bcb8-4c24-9bc3-a7175bdfdfc9
-- title:
--   i Indep Fun: finsets
-- statement:
--   If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise
--   disjoint
--   finite index sets, then the tuples formed by `f i` for `i ∈ S j` are mutually
--   independent,
--   when seen as a family indexed by `J`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L70-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L70-L74

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_Kernel_iIndepFun_finsets

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

theorem ProbabilityTheory.iIndepFun.finsets {f : ∀ i, Ω → β i} {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a (i : S j) ↦ f i a) μ := by sorry
