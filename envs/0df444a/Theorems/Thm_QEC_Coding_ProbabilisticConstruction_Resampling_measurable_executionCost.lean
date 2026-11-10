-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_executionCost
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:30:59.616239+00:00
-- url     : https://prove2.me/theorems/c53ffeaf-f0d2-4ef2-9a33-917ecd910568
-- title:
--   Resampling: measurable execution Cost
-- statement:
--   The Resampling construction uses the measurable execution Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L131-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L131-L144

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionCost (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (outputCost : ℝ≥0∞) :
    Measurable (executionCost vars bad queryCost sampleCost outputCost (X := X)) := by sorry
