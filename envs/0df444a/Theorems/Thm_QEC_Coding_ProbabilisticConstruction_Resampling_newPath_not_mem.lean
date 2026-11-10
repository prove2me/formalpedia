-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_newPath_not_mem
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.newPath_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:16:52.135757+00:00
-- url     : https://prove2.me/theorems/788c5685-9614-4153-b9db-545fa3c36792
-- title:
--   Resampling: new Path not mem
-- statement:
--   The Resampling construction uses the new Path not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L64-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L64-L73

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.newPath_not_mem (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) :
    attachmentParent G root j P h ++ [j] ∉ P := by sorry
