-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_compatible
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurableSet_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:20:29.999374+00:00
-- url     : https://prove2.me/theorems/84eaeffa-3acb-45b6-9695-993ce378182c
-- title:
--   Resampling: measurable Set compatible
-- statement:
--   The Resampling construction uses the measurable Set compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L96-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L96-L110

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurableSet_compatible (hbad : ∀ i, MeasurableSet (bad i))
    (root : I) (P : Finset (List I)) : MeasurableSet (compatible vars bad root P) := by sorry
