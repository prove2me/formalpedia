-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_earlier_nodes_card_eq_counter
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.earlier_nodes_card_eq_counter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:21:26.628226+00:00
-- url     : https://prove2.me/theorems/3317d790-59db-441a-8382-69458f303d95
-- title:
--   Resampling: earlier nodes card eq counter
-- statement:
--   Backward closure includes exactly every earlier use of each represented variable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryCounters.lean#L48-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryCounters.lean#L48-L68

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.earlier_nodes_card_eq_counter (root : I) (L : List I) (p : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root 0 L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) :
    ((timedHistoryWitness (supportGraph vars) root 0 L).filter
      (fun q => v ∈ vars (pathLabel root q.1) ∧ q.2 < p.2)).card =
      historyCounter vars root L p.2 v := by sorry
