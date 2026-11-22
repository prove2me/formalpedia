-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_pi
-- name    : ProbabilityTheory.iIndepFun.pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:24:12.709907+00:00
-- url     : https://prove2.me/theorems/70627b8d-8466-4277-a3ef-7de3401b1a38
-- title:
--   i Indep Fun: pi
-- statement:
--   If a family of functions `(i, j) ↦ f i j` is independent, then the family of
--   function tuples
--   `i ↦ (f i j)ⱼ` is independent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L267-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L267-L322

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

theorem ProbabilityTheory.iIndepFun.pi
    (f_meas : ∀ i j, Measurable (f i j))
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ω j ↦ f i j ω) μ := by sorry
