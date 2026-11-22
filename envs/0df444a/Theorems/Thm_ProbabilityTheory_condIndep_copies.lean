-- Prove2me | Theorems.Thm_ProbabilityTheory_condIndep_copies
-- name    : ProbabilityTheory.condIndep_copies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:23:43.394557+00:00
-- url     : https://prove2.me/theorems/a99f14ae-6c6d-4cc2-bebe-2ce1953b95ce
-- title:
--   Probability Theory: cond Indep copies
-- statement:
--   For `X, Y` random variables, there exist conditionally independent trials `X_1, X_2,
--   Y'`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L168-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean#L168-L303

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

theorem ProbabilityTheory.condIndep_copies
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    [finY : FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω'
      → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib (⟨X₁, Y'⟩) (⟨X, Y⟩) ν μ ∧
      IdentDistrib (⟨X₂, Y'⟩) (⟨X, Y⟩) ν μ := by sorry
