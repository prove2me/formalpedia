-- Prove2me | Theorems.Thm_ThreeSum_LightSwitch_accepts_iff
-- name    : ThreeSum.LightSwitch.accepts_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:42.175216+00:00
-- url     : https://prove2.me/theorems/665bcc20-a311-4cd3-b46a-c40f352565db
-- title:
--   Light Switch: accepts iff
-- statement:
--   The Light Switch construction uses the accepts iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchBounds.lean#L26-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchBounds.lean#L26-L30

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Theorems.Thm_ThreeSum_Switch_accepts_iff

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LightSwitch.accepts_iff (J j r q : ℕ) :
    Switch.accepts J j r q ↔ left J j r ≤ factor J j*cubic r q := by sorry
