-- Prove2me | Theorems.Thm_ThreeSum_Switch_phi_enclosure
-- name    : ThreeSum.Switch.phi_enclosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:50.343195+00:00
-- url     : https://prove2.me/theorems/8a0077d1-c68f-4e10-9b17-6eb540634b3b
-- title:
--   Switch: phi enclosure
-- statement:
--   The Switch construction uses the phi enclosure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L163-L186
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L163-L186

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.phi_enclosure {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    switchThreshold ((j : ℝ) / J) ≤ phi ((switchIndex J j r : ℝ) / r) ∧
      phi ((switchIndex J j r : ℝ) / r) <
        switchThreshold ((j : ℝ) / J) + 9 / r := by sorry
