-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_list_count_eq_history_count
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.list_count_eq_history_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:03.768551+00:00
-- url     : https://prove2.me/theorems/18dbe2d4-a52f-4014-a3a6-9842b81dc6ac
-- title:
--   Resampling: list count eq history count
-- statement:
--   The Resampling construction uses the list count eq history count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L38-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L38-L57

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.list_count_eq_history_count (root i : I) (L : List I) :
    L.count i = ((Finset.range L.length).filter (fun k => historyLabel root L k = i)).card := by sorry
