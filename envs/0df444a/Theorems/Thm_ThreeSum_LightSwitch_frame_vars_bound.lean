-- Prove2me | Theorems.Thm_ThreeSum_LightSwitch_frame_vars_bound
-- name    : ThreeSum.LightSwitch.frame_vars_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:50.220447+00:00
-- url     : https://prove2.me/theorems/039c84ac-8026-45e6-8fe3-886650344c57
-- title:
--   Light Switch: frame vars bound
-- statement:
--   The Light Switch construction uses the frame vars bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitch.lean#L34-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitch.lean#L34-L37

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Definitions.Def_Submission_ThreeSum_LightSwitch
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}

theorem ThreeSum.LightSwitch.frame_vars_bound (hj : j ≤ J) (hq : q ≤ r) :
    ∀ i, |(frame [(J : ℤ),j,r,q]) i| ≤ ((J+r+1001 : ℕ) : ℤ) := by sorry
