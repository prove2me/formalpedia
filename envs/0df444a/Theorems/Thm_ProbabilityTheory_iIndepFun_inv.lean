-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_inv
-- name    : ProbabilityTheory.iIndepFun.inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:43.294865+00:00
-- url     : https://prove2.me/theorems/501e322c-8c34-4f72-9c62-b0d367ce4fa1
-- title:
--   i Indep Fun: inv
-- statement:
--   The i Indep Fun construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L54-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L54-L63

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
variable (i : ι) [Inv (α i)] [MeasurableInv (α i)] [DecidableEq ι]

theorem ProbabilityTheory.iIndepFun.inv
    (h : iIndepFun f μ) : iIndepFun (update f i (f i)⁻¹) μ := by sorry
