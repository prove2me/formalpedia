-- Prove2me | Theorems.Thm_ProbabilityTheory_IndepFun_finsetSum
-- name    : ProbabilityTheory.IndepFun.finsetSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:56.346785+00:00
-- url     : https://prove2.me/theorems/652f8194-4615-4aa1-b472-2735d94795b2
-- title:
--   Indep Fun: finset Sum
-- statement:
--   The Indep Fun construction uses the finset Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L109-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L109-L129

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

theorem ProbabilityTheory.IndepFun.finsetSum
    [m : MeasurableSpace β'] [AddCommMonoid β'] [MeasurableAdd₂ β']
    {f : ι → Ω → β'} {s t : Finset ι} (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i,
      Measurable (f i))
    (h_disj : Disjoint s t) : IndepFun (∑ i ∈ s, f i) (∑ i ∈ t, f i) μ := by sorry
