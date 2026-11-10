-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_executionScanCost
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionScanCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:29:49.544253+00:00
-- url     : https://prove2.me/theorems/79e0d3fc-6aca-40c6-8f72-5361f77e840a
-- title:
--   Resampling: measurable execution Scan Cost
-- statement:
--   The Resampling construction uses the measurable execution Scan Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L117-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L117-L120

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
include hbad

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionScanCost (queryCost : I → ℝ≥0∞) (n : ℕ) :
    Measurable (fun R : Table (X := X) => executionScanCost vars bad queryCost R n) := by sorry
