-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_earlier_nodes_card_eq_rank
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.earlier_nodes_card_eq_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:21:25.114838+00:00
-- url     : https://prove2.me/theorems/281f12f6-2b33-4f92-be4b-142b0d50cc48
-- title:
--   Resampling: earlier nodes card eq rank
-- statement:
--   Earlier stamped nodes and deeper paths are in bijection for a shared variable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryCounters.lean#L21-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryCounters.lean#L21-L45

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.earlier_nodes_card_eq_rank (root : I) (L : List I) (p : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root 0 L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) :
    ((timedHistoryWitness (supportGraph vars) root 0 L).filter
      (fun q => v ∈ vars (pathLabel root q.1) ∧ q.2 < p.2)).card =
      variableRank vars root (historyWitness (supportGraph vars) root L) p.1 v := by sorry
