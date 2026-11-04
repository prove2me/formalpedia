-- Prove2me | Theorems.Thm_ThreeSum_TernaryEndBridge_endStatement_of_solvers
-- name    : ThreeSum.TernaryEndBridge.endStatement_of_solvers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:41:10.750005+00:00
-- url     : https://prove2.me/theorems/84d85a25-6f43-463a-8dcd-950d0f1ca7d1
-- title:
--   Ternary End Bridge: end Statement of solvers
-- statement:
--   An executable solver for every fixed magnitude exponent, together with
--   its own proved running time, gives the exact rational benchmark statement.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEndBridge.lean#L57-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEndBridge.lean#L57-L68

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEndBridge
open Light
noncomputable section

theorem ThreeSum.TernaryEndBridge.endStatement_of_solvers {r : ℚ} (hr : 0 ≤ r)
    (h : ∀ κ : ℕ,
      ∃ (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need),
        Solves s3Task P p T need ∧ PolyNeed need ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
