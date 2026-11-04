-- Prove2me | Theorems.Thm_ThreeSum_LightSwitch_actual_candidates_nonempty
-- name    : ThreeSum.LightSwitch.actual_candidates_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:38.10472+00:00
-- url     : https://prove2.me/theorems/5a8744fd-f21e-4d4a-b7e1-dafc1d7ebef6
-- title:
--   Light Switch: actual candidates nonempty
-- statement:
--   The Light Switch construction uses the actual candidates nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchBounds.lean#L51-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchBounds.lean#L51-L64

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Theorems.Thm_ThreeSum_Scales_actual_candidates_nonempty

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LightSwitch.actual_candidates_nonempty {n j : ℕ} (hj : j ≤ Switch.terminalDepth n) :
    (Switch.candidates (Scales.blockCount (Scales.inputBits n)) j
      (Switch.residualSize n j)).Nonempty := by sorry
