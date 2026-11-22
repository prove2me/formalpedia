-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_iIndepFun_pi__7fb5b683b8a2
-- name    : P2M_ProbabilityTheory_iIndepFun_pi__7fb5b683b8a2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:46.985522+00:00
-- url     : https://prove2.me/theorems/75721562-1793-4203-b7da-78b69db965c1
-- title:
--   P2 M Probability Theory i Indep Fun pi  7fb5b683b8a2: P2 M Probability Theory i Indep Fun pi  7fb5b683b8a2
-- statement:
--   If a family of functions `(i, j) ↦ f i j` is independent, then the family of
--   function tuples
--   `i ↦ (f i j)ⱼ` is independent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L328-L332
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L328-L332

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

theorem P2M_ProbabilityTheory_iIndepFun_pi__7fb5b683b8a2 {f : ∀ ij : (Σ i, κ i), Ω → α ij.1 ij.2 }
    (f_meas : ∀ i, Measurable (f i))
    (hf : iIndepFun f μ) :
    iIndepFun (fun i ω ↦ (fun j ↦ f ⟨i, j⟩ ω)) μ := by sorry

alias «ProbabilityTheory».«iIndepFun».«pi'» := P2M_ProbabilityTheory_iIndepFun_pi__7fb5b683b8a2
