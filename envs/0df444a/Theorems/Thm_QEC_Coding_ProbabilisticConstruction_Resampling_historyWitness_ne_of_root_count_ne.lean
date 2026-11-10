-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_ne_of_root_count_ne
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_ne_of_root_count_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:00.600261+00:00
-- url     : https://prove2.me/theorems/ea38ff58-2af3-4448-8bff-d13301d487bd
-- title:
--   Resampling: history Witness ne of root count ne
-- statement:
--   Different occurrence numbers cannot share a root witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L184-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L184-L189

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_ne_of_root_count_ne (root : I) (L K : List I)
    (h : L.count root ≠ K.count root) : historyWitness G root L ≠ historyWitness G root K := by sorry
