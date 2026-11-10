-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_compatible
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:22:31.447008+00:00
-- url     : https://prove2.me/theorems/429cf4bd-0851-48c7-981b-fe2f1bb64291
-- title:
--   Resampling: occurrence History compatible
-- statement:
--   Compatibility for the witness extracted from an actual selected occurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L108-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L108-L114

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_compatible (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) :
    R ∈ compatible vars bad i
      (historyWitness (supportGraph vars) i (occurrenceHistory vars bad R n i hi)) := by sorry
