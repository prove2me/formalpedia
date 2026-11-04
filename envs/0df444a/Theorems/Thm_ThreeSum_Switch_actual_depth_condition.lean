-- Prove2me | Theorems.Thm_ThreeSum_Switch_actual_depth_condition
-- name    : ThreeSum.Switch.actual_depth_condition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:45.593033+00:00
-- url     : https://prove2.me/theorems/02652918-5dab-430c-84b0-c06125ac6c64
-- title:
--   Switch: actual depth condition
-- statement:
--   The Switch construction uses the actual depth condition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L193-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L193-L197

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.actual_depth_condition {n j : ℕ} (hj : j ≤ terminalDepth n) :
    20 * j ≤ 13 * blockCount (inputBits n) := by sorry
