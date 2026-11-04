-- Prove2me | Theorems.Thm_ThreeSum_BudgetTime_endStatementBigO_of_eventually_le_rpow
-- name    : ThreeSum.BudgetTime.endStatementBigO_of_eventually_le_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:21:54.664016+00:00
-- url     : https://prove2.me/theorems/49c0432e-2d0f-4c06-8391-21644dbacf7e
-- title:
--   Budget Time: end Statement Big O of eventually le rpow
-- statement:
--   A genuinely eventual estimate suffices for the benchmark's bound at
--   every `n ≥ 2`: the finite exceptional values enter its constant.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L41-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L41-L60

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000

theorem ThreeSum.BudgetTime.endStatementBigO_of_eventually_le_rpow {r : ℚ} {T : ℕ → ℕ}
    (hr : 0 ≤ r)
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.BigO T r := by sorry
