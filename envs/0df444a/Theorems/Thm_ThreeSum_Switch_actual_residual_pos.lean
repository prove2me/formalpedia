-- Prove2me | Theorems.Thm_ThreeSum_Switch_actual_residual_pos
-- name    : ThreeSum.Switch.actual_residual_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:19.710014+00:00
-- url     : https://prove2.me/theorems/815c5d73-fdbb-49c0-9788-ae7c7f3b0da9
-- title:
--   Switch: actual residual pos
-- statement:
--   The Switch construction uses the actual residual pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L199-L204
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L199-L204

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.actual_residual_pos {n j : ℕ} (hmu : 0 < mu n) (hj : j ≤ terminalDepth n) :
    0 < residualSize n j := by sorry
