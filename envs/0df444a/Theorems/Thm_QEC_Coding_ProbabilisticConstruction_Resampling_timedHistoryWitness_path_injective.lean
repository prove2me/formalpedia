-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_path_injective
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_path_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:57.30591+00:00
-- url     : https://prove2.me/theorems/02b6fba7-3c71-41f5-9695-8ff2be46fd21
-- title:
--   Resampling: timed History Witness path injective
-- statement:
--   Every represented path has a unique time stamp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L62-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L62-L85

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_path_injective (root : I) (offset : ℕ) (L : List I) :
    Set.InjOn Prod.fst (timedHistoryWitness G root offset L : Set (List I × ℕ)) := by sorry
