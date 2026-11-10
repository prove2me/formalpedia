-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_expected_executionCost_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.expected_executionCost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-09T19:31:05.44524+00:00
-- url     : https://prove2.me/theorems/ee158afa-ca33-4146-bd7c-6a738570aa02
-- title:
--   Resampling: expected execution Cost le
-- statement:
--   Explicit idealized expected cost, including initialization, the last scan, and output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L152-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L152-L174

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
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
include hbad hx0 hx1 hcrit

theorem QEC.Coding.ProbabilisticConstruction.Resampling.expected_executionCost_le (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (initialCost outputCost C : ℝ≥0∞) (hinit : ∑ v, sampleCost v ≤ initialCost)
    (hquery : ∀ i, queryCost i ≤ C)
    (hsample : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q) :
    (∫⁻ R, executionCost vars bad queryCost sampleCost outputCost R ∂tableLaw ν) ≤
      initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) *
          ENNReal.ofReal (∑ i, resamplingBudget x i) := by sorry
