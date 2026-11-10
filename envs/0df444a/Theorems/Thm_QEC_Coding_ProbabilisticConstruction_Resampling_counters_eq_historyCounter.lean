-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_eq_historyCounter
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.counters_eq_historyCounter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:22:36.121205+00:00
-- url     : https://prove2.me/theorems/f3d15b49-f37d-4f3f-a42d-443eb34c18fc
-- title:
--   Resampling: counters eq history Counter
-- statement:
--   An actual finite log determines each table counter by counting prior support uses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L63-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L63-L72

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.counters_eq_historyCounter (R : Table (X := X)) (root : I) (L : List I)
    (hlog : ∀ k ≤ L.length, selected vars bad R k = some (historyLabel root L k))
    (n : ℕ) (hn : n ≤ L.length) (v : V) :
    counters vars bad R n v = historyCounter vars root L n v := by sorry
