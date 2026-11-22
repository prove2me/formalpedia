-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_iIndepFun_finsets_comp
-- name    : ProbabilityTheory.Kernel.iIndepFun.finsets_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:23.067191+00:00
-- url     : https://prove2.me/theorems/b0877f39-c37f-4931-8b1c-1fca77bd1be4
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
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Kernel/IndepFun.lean#L155-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Kernel/IndepFun.lean#L155-L161

module
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasurableSpace
open scoped MeasureTheory ENNReal
open ProbabilityTheory ProbabilityTheory.Kernel
variable {ι α β β' γ γ' Ω : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}
variable {β γ : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {mγ : ∀ i,
  MeasurableSpace (γ i)}
  {f : ∀ i, Ω → β i}

theorem ProbabilityTheory.Kernel.iIndepFun.finsets_comp {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i))
    (γ : J → Type*) {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) κ μ := by sorry
