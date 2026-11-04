-- Prove2me | Theorems.Thm_ThreeSum_Switch_residual_real_identity
-- name    : ThreeSum.Switch.residual_real_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:32.325551+00:00
-- url     : https://prove2.me/theorems/7fe578a6-eeb3-4396-9a8d-b5c3c894f640
-- title:
--   Switch: residual real identity
-- statement:
--   The Switch construction uses the residual real identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L206-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L206-L217

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.residual_real_identity {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    (residualSize n j : ℝ) =
      (1 - (j : ℝ) / blockCount (inputBits n)) * mu n := by sorry
