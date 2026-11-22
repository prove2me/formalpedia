-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_ae_eq
-- name    : ProbabilityTheory.iIndepFun.ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:28:12.320685+00:00
-- url     : https://prove2.me/theorems/d8bf036d-6c31-4bf7-b273-de33c3e05542
-- title:
--   i Indep Fun: ae eq
-- statement:
--   TODO: a kernel version of this theorem
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L364-L394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L364-L394

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

theorem ProbabilityTheory.iIndepFun.ae_eq {ι : Type*} {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f g : ∀ i, Ω → β i}
    (hf_Indep : iIndepFun f μ) (hfg : ∀ i, f i =ᵐ[μ] g i) : iIndepFun g μ := by sorry
