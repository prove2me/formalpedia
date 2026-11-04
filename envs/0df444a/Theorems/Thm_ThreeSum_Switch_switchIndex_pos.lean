-- Prove2me | Theorems.Thm_ThreeSum_Switch_switchIndex_pos
-- name    : ThreeSum.Switch.switchIndex_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:13:43.679646+00:00
-- url     : https://prove2.me/theorems/3f4d19d8-d3a1-49fe-b509-fe479eafb91d
-- title:
--   Switch: switch Index pos
-- statement:
--   The Switch construction uses the switch Index pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L125-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L125-L133

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.switchIndex_pos {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : 0 < switchIndex J j r := by sorry
