-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_executionRefreshCost
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionRefreshCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:29:52.627738+00:00
-- url     : https://prove2.me/theorems/b2e1195f-7de3-466d-8723-aa7563ff0334
-- title:
--   Resampling: measurable execution Refresh Cost
-- statement:
--   The Resampling construction uses the measurable execution Refresh Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L123-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L123-L128

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionRefreshCost (sampleCost : V → ℝ≥0∞) (n : ℕ) :
    Measurable (fun R : Table (X := X) => executionRefreshCost vars bad sampleCost R n) := by sorry
