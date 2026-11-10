-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_depth_time
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_depth_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:48.315222+00:00
-- url     : https://prove2.me/theorems/53bde2cd-5185-48a4-addb-5f641f930f06
-- title:
--   Resampling: timed History Witness depth time
-- statement:
--   Shared-variable nodes are ordered by depth in exactly the reverse chronological order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L146-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L146-L181

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_depth_time (root : I) (offset : ℕ) (L : List I)
    (p q : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (hq : q ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) (hqv : v ∈ vars (pathLabel root q.1)) :
    p.2 < q.2 ↔ q.1.length < p.1.length := by sorry
