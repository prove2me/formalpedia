-- Prove2me | Theorems.Thm_ThreeSum_Switch_predecessor_rejected
-- name    : ThreeSum.Switch.predecessor_rejected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:46.712807+00:00
-- url     : https://prove2.me/theorems/76162bbe-5dc4-401a-b5b9-909eef9c69ca
-- title:
--   Switch: predecessor rejected
-- statement:
--   The Switch construction uses the predecessor rejected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L135-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L135-L144

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.predecessor_rejected {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    ¬ accepts J j r (switchIndex J j r - 1) := by sorry
