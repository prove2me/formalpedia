-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_succ_of_some
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.counters_succ_of_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:57.235195+00:00
-- url     : https://prove2.me/theorems/ade83bb2-120d-4edf-8de8-52819764c835
-- title:
--   Resampling: counters succ of some
-- statement:
--   The Resampling construction uses the counters succ of some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L159-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L159-L163

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.counters_succ_of_some (R : Table (X := X)) (n : ℕ) (i : I)
    (h : selected vars bad R n = some i) :
    counters vars bad R (n + 1) = advance vars i (counters vars bad R n) := by sorry
