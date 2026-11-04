-- Prove2me | Theorems.Thm_ThreeSum_Switch_switch_ratio_mem
-- name    : ThreeSum.Switch.switch_ratio_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:13:55.237681+00:00
-- url     : https://prove2.me/theorems/c32b88a9-814f-4f8e-adaf-561ccf1e15a9
-- title:
--   Switch: switch ratio mem
-- statement:
--   The Switch construction uses the switch ratio mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L158-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L158-L161

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.switch_ratio_mem {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    (switchIndex J j r : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) := by sorry
