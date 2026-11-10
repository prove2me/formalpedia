-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_paths
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_paths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:35.018525+00:00
-- url     : https://prove2.me/theorems/ace7eea5-5b5e-4c76-b5ef-5108ea1b0095
-- title:
--   Resampling: timed History Witness paths
-- statement:
--   The Resampling construction uses the timed History Witness paths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L25-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L25-L32

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_paths (root : I) (offset : ℕ) (L : List I) :
    (timedHistoryWitness G root offset L).image Prod.fst = historyWitness G root L := by sorry
