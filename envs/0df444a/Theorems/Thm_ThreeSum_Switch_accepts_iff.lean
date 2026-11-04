-- Prove2me | Theorems.Thm_ThreeSum_Switch_accepts_iff
-- name    : ThreeSum.Switch.accepts_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:59.519808+00:00
-- url     : https://prove2.me/theorems/fbad2a09-51ca-411f-a2d6-5c16019e445c
-- title:
--   Switch: accepts iff
-- statement:
--   The Switch construction uses the accepts iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L92-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L92-L103

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.accepts_iff {J j r q : ℕ} (hJ : 0 < J) (hj : j < J) (hr : 0 < r) :
    accepts J j r q ↔ switchThreshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / r) := by sorry
