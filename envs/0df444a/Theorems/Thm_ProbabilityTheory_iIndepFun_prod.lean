-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_prod
-- name    : ProbabilityTheory.iIndepFun.prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:42.070799+00:00
-- url     : https://prove2.me/theorems/1c3d2ab4-2c51-4c47-bb31-7a32dfb9b279
-- title:
--   i Indep Fun: prod
-- statement:
--   The i Indep Fun construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L337-L351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L337-L351

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
variable {ι : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
  {α : ∀ i, κ i → Type*} {f : ∀ i j, Ω → α i j} [m : ∀ i j, MeasurableSpace (α i j)]
variable {ι ι' : Type*} {α : ι → Type*}
    {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}

theorem ProbabilityTheory.iIndepFun.prod
    {hf : ∀ (i : ι), Measurable (f i)} {ST : ι' → Finset ι}
    (hS : Pairwise (Disjoint on ST)) (h : iIndepFun f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := by sorry
