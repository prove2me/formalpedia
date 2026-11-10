-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_executionCost_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.executionCost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-09T19:29:44.445483+00:00
-- url     : https://prove2.me/theorems/7fdb5d1e-12c5-4f0b-a2c1-b7874758778f
-- title:
--   Resampling: execution Cost le
-- statement:
--   Primitive bounds give a pointwise affine cost bound for every terminating run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L92-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L92-L110

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.executionCost_le (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (initialCost outputCost C : ℝ≥0∞) (hinit : ∑ v, sampleCost v ≤ initialCost)
    (hquery : ∀ i, queryCost i ≤ C)
    (hsample : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q)
    (R : Table (X := X)) (hR : Halts vars bad R) :
    executionCost vars bad queryCost sampleCost outputCost R ≤
      initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) * totalSteps vars bad R := by sorry
