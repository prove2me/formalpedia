-- Prove2me | Theorems.Thm_ProbabilityTheory_EventuallyEq_finite_iInter
-- name    : ProbabilityTheory.EventuallyEq.finite_iInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:50.143797+00:00
-- url     : https://prove2.me/theorems/10d16ae0-214f-45ba-b739-050d145bca63
-- title:
--   Eventually Eq: finite i Inter
-- statement:
--   The Mathlib tool `Finset.eventuallyEqSet_iInter` supersedes this result.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L356-L361
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L356-L361

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
variable {β β' Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem ProbabilityTheory.EventuallyEq.finite_iInter
    {ι : Type*} {α : Type u_2} {l : Filter α} (s : Finset ι)
    {E : ι → Set α} {F : ι → Set α}
    (h : ∀ i ∈ s, E i =ᶠ[l] F i) :
    ⋂ i ∈ s, E i =ᶠ[l] ⋂ i ∈ s, F i := by sorry
