-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_shared_depth_injective
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_shared_depth_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:18:46.745942+00:00
-- url     : https://prove2.me/theorems/1b8aa684-e394-4bf9-868f-2e1a20456d43
-- title:
--   Resampling: history Witness shared depth injective
-- statement:
--   The history construction never puts two nodes sharing a variable at the same depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L184-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L184-L195

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_shared_depth_injective (root : I) (L : List I)
    (p q : List I) (hp : p ∈ historyWitness (supportGraph vars) root L)
    (hq : q ∈ historyWitness (supportGraph vars) root L)
    (v : V) (hpv : v ∈ vars (pathLabel root p)) (hqv : v ∈ vars (pathLabel root q))
    (hd : p.length = q.length) : p = q := by sorry
