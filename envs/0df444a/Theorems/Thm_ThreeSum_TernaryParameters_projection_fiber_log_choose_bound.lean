-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_projection_fiber_log_choose_bound
-- name    : ThreeSum.TernaryParameters.projection_fiber_log_choose_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:08.946294+00:00
-- url     : https://prove2.me/theorems/12bcd114-bd7e-4bc0-a4e7-2c6fe862607b
-- title:
--   Ternary Parameters: projection fiber log choose bound
-- statement:
--   Exact finite bound on the mixed projection fiber in the integer schedule.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L417-L437
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L417-L437

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem ThreeSum.TernaryParameters.projection_fiber_log_choose_bound {m : ℕ} (hm : 0 < m) :
    Real.log (((100000000 * m).choose (978268 * m) : ℕ) : ℝ) <
      (100000000 * m : ℕ) * Real.log 2 / 4 := by sorry
