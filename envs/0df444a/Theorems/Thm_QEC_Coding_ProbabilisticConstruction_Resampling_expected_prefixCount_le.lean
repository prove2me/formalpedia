-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_expected_prefixCount_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.expected_prefixCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:34.940849+00:00
-- url     : https://prove2.me/theorems/efb11d0b-1d1c-4e66-ab64-28fdb54f4376
-- title:
--   Resampling: expected prefix Count le
-- statement:
--   Every finite prefix obeys the same asymmetric resampling expectation budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L48-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L48-L81

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.expected_prefixCount_le (T : ℕ) (i : I) :
    (∫⁻ R, (prefixCount vars bad R T i : ℝ≥0∞) ∂tableLaw ν) ≤
      ENNReal.ofReal (resamplingBudget x i) := by sorry
