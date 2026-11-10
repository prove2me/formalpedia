-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_expected_totalSteps_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.expected_totalSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:31.571613+00:00
-- url     : https://prove2.me/theorems/dda637c2-cdbf-4884-9361-b229f9a04558
-- title:
--   Resampling: expected total Steps le
-- statement:
--   Summing the per-event budgets bounds the actual total resampling expectation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L112-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L112-L118

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
include hbad hx0 hx1 hcrit

theorem QEC.Coding.ProbabilisticConstruction.Resampling.expected_totalSteps_le :
    (∫⁻ R, totalSteps vars bad R ∂tableLaw ν) ≤
      ENNReal.ofReal (∑ i, resamplingBudget x i) := by sorry
