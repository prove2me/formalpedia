-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_succ_of_none
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.counters_succ_of_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:23.446204+00:00
-- url     : https://prove2.me/theorems/90169f23-7656-4b81-85d9-2fa7f7857667
-- title:
--   Resampling: counters succ of none
-- statement:
--   The Resampling construction uses the counters succ of none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L153-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L153-L157

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.counters_succ_of_none (R : Table (X := X)) (n : ℕ)
    (h : selected vars bad R n = none) :
    counters vars bad R (n + 1) = counters vars bad R n := by sorry
