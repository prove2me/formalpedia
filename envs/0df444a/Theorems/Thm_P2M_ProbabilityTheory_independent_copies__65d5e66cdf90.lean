-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_independent_copies__65d5e66cdf90
-- name    : P2M_ProbabilityTheory_independent_copies__65d5e66cdf90
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:24:49.420635+00:00
-- url     : https://prove2.me/theorems/fa6edf81-e1f4-487a-96d3-85f9ce0d8734
-- title:
--   P2 M Probability Theory independent copies  65d5e66cdf90: P2 M Probability Theory independent copies  65d5e66cdf90
-- statement:
--   Let `Xᵢ : Ωᵢ → Sᵢ` be random variables for `i = 1,...,k`.
--   Then there exist jointly independent random variables `Xᵢ' : Ω' → Sᵢ` for `i=1,...,k`
--   such that each `Xᵢ'` is a copy of `Xᵢ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L322-L340
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L322-L340

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal
attribute [symm] ProbabilityTheory.IdentDistrib.symm
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]
open MeasureTheory ProbabilityTheory Function Set
open ProbabilityTheory
universe u u' v
variable {Ω Ω' α ι β β' T : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω
    → β} {f' g' : Ω' → β}
variable [MeasurableSpace α] [MeasurableSpace β]

theorem P2M_ProbabilityTheory_independent_copies__65d5e66cdf90 {I : Type u} [Finite I] {α : I → Type u'}
    [mS : ∀ i : I, MeasurableSpace (α i)] {Ω : I → Type v}
    [mΩ : ∀ i : I, MeasurableSpace (Ω i)] (X : ∀ i : I, Ω i → α i) (hX : ∀ i : I,
      Measurable (X i))
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ (A : Type (max u v)) (_ : MeasurableSpace A) (μA : Measure A) (X' : ∀ i, A → α i),
    IsProbabilityMeasure μA ∧ iIndepFun X' μA ∧
    ∀ i : I, Measurable (X' i) ∧ IdentDistrib (X' i) (X i) μA (μ i) := by sorry

alias «ProbabilityTheory».«independent_copies'» := P2M_ProbabilityTheory_independent_copies__65d5e66cdf90
