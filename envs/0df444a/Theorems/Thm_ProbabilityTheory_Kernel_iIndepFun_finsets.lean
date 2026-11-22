-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_iIndepFun_finsets
-- name    : ProbabilityTheory.Kernel.iIndepFun.finsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:24.218435+00:00
-- url     : https://prove2.me/theorems/2f9c83a3-129f-46a4-869c-a1e7bec8c4e4
-- title:
--   i Indep Fun: finsets
-- statement:
--   If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise
--   disjoint
--   finite index sets, then the tuples formed by `f i` for `i ∈ S j` are mutually
--   independent,
--   when seen as a family indexed by `J`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Kernel/IndepFun.lean#L42-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Kernel/IndepFun.lean#L42-L146

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

theorem ProbabilityTheory.Kernel.iIndepFun.finsets {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a (i : S j) ↦ f i a) κ μ := by sorry
