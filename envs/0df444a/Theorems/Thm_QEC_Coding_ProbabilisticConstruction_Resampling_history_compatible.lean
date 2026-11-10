-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_history_compatible
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.history_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:23:36.455649+00:00
-- url     : https://prove2.me/theorems/22c92d28-1b64-4ca5-9297-3d81b3351681
-- title:
--   Resampling: history compatible
-- statement:
--   Every node of a real history witness reads the same table entries as its execution step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L75-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L75-L105

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.history_compatible (R : Table (X := X)) (root : I) (L : List I)
    (hlog : ∀ k ≤ L.length, selected vars bad R k = some (historyLabel root L k)) :
    R ∈ compatible vars bad root (historyWitness (supportGraph vars) root L) := by sorry
