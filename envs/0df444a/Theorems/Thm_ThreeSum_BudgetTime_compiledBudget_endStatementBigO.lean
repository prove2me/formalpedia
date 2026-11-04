-- Prove2me | Theorems.Thm_ThreeSum_BudgetTime_compiledBudget_endStatementBigO
-- name    : ThreeSum.BudgetTime.compiledBudget_endStatementBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:54:54.768654+00:00
-- url     : https://prove2.me/theorems/852a9ca2-7920-48f3-82c3-512f5043b138
-- title:
--   Budget Time: compiled Budget end Statement Big O
-- statement:
--   The Budget Time construction uses the compiled Budget end Statement Big O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L86-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L86-L89

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000

theorem ThreeSum.BudgetTime.compiledBudget_endStatementBigO (a b C k : ℕ) :
    EndStatement.BigO (compiledBudget a b C k) (981 / 500) := by sorry
