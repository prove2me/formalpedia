-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_refreshed_columns_strict
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.refreshed_columns_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:55.199457+00:00
-- url     : https://prove2.me/theorems/d2865898-6317-4457-82a4-ef9b6bab892b
-- title:
--   Resampling: refreshed columns strict
-- statement:
--   A refreshed column is newer than every column read after an earlier transition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L190-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L190-L194

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.refreshed_columns_strict (R : Table (X := X)) (n m : ℕ) (hnm : n < m)
    (i : I) (hm : selected vars bad R m = some i) {v : V} (hv : v ∈ vars i) :
    counters vars bad R (n + 1) v < counters vars bad R (m + 1) v := by sorry
