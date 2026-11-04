-- Prove2me | Theorems.Thm_ThreeSum_BudgetTime_time_endStatementBigO_of_eventually_le_compiledBudget
-- name    : ThreeSum.BudgetTime.time_endStatementBigO_of_eventually_le_compiledBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:24.844035+00:00
-- url     : https://prove2.me/theorems/8eae30e1-12fa-407d-8185-07504572f18c
-- title:
--   Budget Time: time end Statement Big O of eventually le compiled Budget
-- statement:
--   This theorem requires the cost of an actual program (or another concrete
--   natural-valued cost) to have been bounded separately.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L93-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L93-L100

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000

theorem ThreeSum.BudgetTime.time_endStatementBigO_of_eventually_le_compiledBudget
    {T : ℕ → ℕ} {a b C k : ℕ}
    (hT : ∀ᶠ n : ℕ in atTop, T n ≤ compiledBudget a b C k n) :
    EndStatement.BigO T (981 / 500) := by sorry
