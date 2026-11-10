-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_totalCount
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_totalCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:21.005004+00:00
-- url     : https://prove2.me/theorems/d80395ca-2480-452b-87ab-6e11bb0715e6
-- title:
--   Resampling: measurable total Count
-- statement:
--   The Resampling construction uses the measurable total Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L88-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L88-L90

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
include hbad

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_totalCount (i : I) :
    Measurable (fun R : Table (X := X) => totalCount vars bad R i) := by sorry
