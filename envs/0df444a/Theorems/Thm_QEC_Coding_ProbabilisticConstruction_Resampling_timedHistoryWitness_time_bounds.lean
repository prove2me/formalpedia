-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_time_bounds
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_time_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:28.432232+00:00
-- url     : https://prove2.me/theorems/a8777cde-4b4c-4831-a851-5c47626f5e23
-- title:
--   Resampling: timed History Witness time bounds
-- statement:
--   The Resampling construction uses the timed History Witness time bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L46-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L46-L59

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_time_bounds (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness G root offset L) :
    offset ≤ p.2 ∧ p.2 ≤ offset + L.length := by sorry
