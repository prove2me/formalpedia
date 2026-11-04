-- Prove2me | Theorems.Thm_ThreeSum_Switch_depth_fraction
-- name    : ThreeSum.Switch.depth_fraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:13:42.955204+00:00
-- url     : https://prove2.me/theorems/1a25f3b8-ade1-425b-a4f8-41e8243cbe99
-- title:
--   Switch: depth fraction
-- statement:
--   The Switch construction uses the depth fraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L58-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L58-L66

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.depth_fraction {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) :
    (j : ℝ) / J ∈ Icc (0 : ℝ) terminalFraction := by sorry
