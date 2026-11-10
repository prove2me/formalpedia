-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_time_injective
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_time_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:40.571452+00:00
-- url     : https://prove2.me/theorems/5c3ff304-8608-47c1-93a1-4abdcae8422f
-- title:
--   Resampling: timed History Witness time injective
-- statement:
--   No two represented nodes originate at the same actual resampling time.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L88-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L88-L105

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_time_injective (root : I) (offset : ℕ) (L : List I) :
    Set.InjOn Prod.snd (timedHistoryWitness G root offset L : Set (List I × ℕ)) := by sorry
