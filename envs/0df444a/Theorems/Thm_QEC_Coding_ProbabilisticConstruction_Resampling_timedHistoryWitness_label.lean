-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_label
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:18:52.983435+00:00
-- url     : https://prove2.me/theorems/f069adc0-d8d5-40e3-9b42-534740931f38
-- title:
--   Resampling: timed History Witness label
-- statement:
--   The Resampling construction uses the timed History Witness label property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L110-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L110-L127

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_label (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness G root offset L) :
    pathLabel root p.1 = historyLabel root L (p.2 - offset) := by sorry
