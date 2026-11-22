-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_condIndep_copies__84a4bd00618a
-- name    : P2M_ProbabilityTheory_condIndep_copies__84a4bd00618a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:29:59.874801+00:00
-- url     : https://prove2.me/theorems/a7913d7a-6309-40b2-91fd-ce6c7701c82c
-- title:
--   P2 M Probability Theory cond Indep copies  84a4bd00618a: P2 M Probability Theory cond Indep copies  84a4bd00618a
-- statement:
--   For `X, Y` random variables, there exist conditionally independent trials `X₁, X₂, Y'`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L308-L334
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L308-L334

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Measure Set
open scoped ENNReal ZhangYeungPFR
open ProbabilityTheory
universe u
variable {Ω : Type*} {α β :
  Type u} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
variable [Countable β]
open Function Set Measure

theorem P2M_ProbabilityTheory_condIndep_copies__84a4bd00618a
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : α → β → Prop)
    (hp : Measurable (uncurry p)) (hp' : ∀ᵐ ω ∂μ, p (X ω) (Y ω)) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω'
      → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib (⟨X₁, Y'⟩) (⟨X, Y⟩) ν μ ∧
       IdentDistrib (⟨X₂, Y'⟩) (⟨X, Y⟩) ν μ ∧ (∀ ω,
         p (X₁ ω) (Y' ω)) ∧ (∀ ω, p (X₂ ω) (Y' ω)) := by sorry

alias «ProbabilityTheory».«condIndep_copies'» := P2M_ProbabilityTheory_condIndep_copies__84a4bd00618a
