-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_newPath_deeper_than_candidate
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.newPath_deeper_than_candidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:16:50.906749+00:00
-- url     : https://prove2.me/theorems/ca37e341-b864-4dd5-9fed-26a0a83b9c28
-- title:
--   Resampling: new Path deeper than candidate
-- statement:
--   Inserting a dependency puts the new node deeper than every node it touches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L96-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L96-L102

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.newPath_deeper_than_candidate (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) (q : List I)
    (hq : q ∈ attachmentCandidates G root j P) :
    q.length < (attachmentParent G root j P h ++ [j]).length := by sorry
