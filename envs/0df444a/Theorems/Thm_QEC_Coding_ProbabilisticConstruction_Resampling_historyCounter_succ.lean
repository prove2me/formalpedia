-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyCounter_succ
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.historyCounter_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:22:18.372362+00:00
-- url     : https://prove2.me/theorems/97e39e35-e776-4528-bd09-deaebff3cb52
-- title:
--   Resampling: history Counter succ
-- statement:
--   The Resampling construction uses the history Counter succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L54-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean#L54-L60

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.historyCounter_succ (root : I) (L : List I) (n : ℕ) (v : V) :
    historyCounter vars root L (n + 1) v = historyCounter vars root L n v +
      if v ∈ vars (historyLabel root L n) then 1 else 0 := by sorry
