-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:22:30.451432+00:00
-- url     : https://prove2.me/theorems/7ba3880a-bb10-401e-91ca-126648bb066c
-- title:
--   Resampling: occurrence History length
-- statement:
--   The Resampling construction uses the occurrence History length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L35-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L35-L38

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) :
    (occurrenceHistory vars bad R n i hi).length = n := by sorry
