-- Prove2me | Theorems.Thm_ThreeSum_BudgetTime_workBudget_endStatementBigO
-- name    : ThreeSum.BudgetTime.workBudget_endStatementBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:54:45.732035+00:00
-- url     : https://prove2.me/theorems/73fb51de-1765-4906-8a44-be842980d611
-- title:
--   Budget Time: work Budget end Statement Big O
-- statement:
--   The Budget Time construction uses the work Budget end Statement Big O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L62-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L62-L65

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000

theorem ThreeSum.BudgetTime.workBudget_endStatementBigO (C k : ℕ) :
    EndStatement.BigO (workBudget C k) (981 / 500) := by sorry
