-- Prove2me | Theorems.Thm_ThreeSum_TernaryEndBridge_timeUpTo_eventually_of_uniform
-- name    : ThreeSum.TernaryEndBridge.timeUpTo_eventually_of_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:41:19.033238+00:00
-- url     : https://prove2.me/theorems/5f5a31dd-c52f-4708-92ee-347c7bef4241
-- title:
--   Ternary End Bridge: time Up To eventually of uniform
-- statement:
--   A uniform natural bound on the actual admissible magnitude parameters
--   also bounds the real finite supremum used by the existing compiler.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEndBridge.lean#L39-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEndBridge.lean#L39-L53

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEndBridge
open Light
noncomputable section

theorem ThreeSum.TernaryEndBridge.timeUpTo_eventually_of_uniform {κ : ℕ} {T : ℕ → ℕ → ℕ} {a : ℝ}
    (ht : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ U : ℕ, U ≤ n ^ κ → (T n U : ℝ) ≤ (n : ℝ) ^ a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ a := by sorry
