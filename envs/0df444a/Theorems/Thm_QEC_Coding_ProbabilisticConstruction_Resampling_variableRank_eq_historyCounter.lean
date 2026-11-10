-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_variableRank_eq_historyCounter
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_eq_historyCounter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:21:16.33735+00:00
-- url     : https://prove2.me/theorems/d6bd7ba4-a647-42fb-9173-1743d95fc2d4
-- title:
--   Resampling: variable Rank eq history Counter
-- statement:
--   Compatibility reads the exact actual-history column at every represented node.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryCounters.lean#L71-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryCounters.lean#L71-L77

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_eq_historyCounter (root : I) (L : List I) (p : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root 0 L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) :
    variableRank vars root (historyWitness (supportGraph vars) root L) p.1 v =
      historyCounter vars root L p.2 v := by sorry
