-- Prove2me | Theorems.Thm_ThreeSum_BudgetTime_rational_rpow_power
-- name    : ThreeSum.BudgetTime.rational_rpow_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:19.637556+00:00
-- url     : https://prove2.me/theorems/1b9e4118-4ff3-429f-85f5-d0a748e93bfe
-- title:
--   Budget Time: rational rpow power
-- statement:
--   Raising a nonnegative rational power to its denominator gives the
--   corresponding natural-number numerator power.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L28-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L28-L37

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000

theorem ThreeSum.BudgetTime.rational_rpow_power {r : ℚ} (hr : 0 ≤ r) (n : ℕ) :
    ((n : ℝ) ^ (r : ℝ)) ^ r.den = (n : ℝ) ^ r.num.toNat := by sorry
