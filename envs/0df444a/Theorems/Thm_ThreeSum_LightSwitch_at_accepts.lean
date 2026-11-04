-- Prove2me | Theorems.Thm_ThreeSum_LightSwitch_at_accepts
-- name    : ThreeSum.LightSwitch.at_accepts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:44.26007+00:00
-- url     : https://prove2.me/theorems/10f0d820-2cec-44c0-bad1-df8efeb7102e
-- title:
--   Light Switch: at accepts
-- statement:
--   The Light Switch construction uses the at accepts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchBounds.lean#L43-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchBounds.lean#L43-L45

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LightSwitch.at_accepts {J j r : ℕ} (hne : (Switch.candidates J j r).Nonempty) :
    left J j r ≤ factor J j*cubic r (Switch.switchIndex J j r) := by sorry
