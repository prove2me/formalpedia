-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_earlier_variable
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_earlier_variable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:19:02.63552+00:00
-- url     : https://prove2.me/theorems/78a8da2d-a897-499b-b86a-6877a19e04ae
-- title:
--   Resampling: timed History Witness earlier variable
-- statement:
--   Every earlier use of a node's variable is included in its backward witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L198-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L198-L235

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_earlier_variable (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) (k : ℕ)
    (hk : offset ≤ k) (hkp : k < p.2)
    (hkv : v ∈ vars (historyLabel root L (k - offset))) :
    ∃ q ∈ timedHistoryWitness (supportGraph vars) root offset L,
      q.2 = k ∧ v ∈ vars (pathLabel root q.1) := by sorry
