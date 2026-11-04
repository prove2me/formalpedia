-- Prove2me | Theorems.Thm_ThreeSum_Switch_actual_totalSize
-- name    : ThreeSum.Switch.actual_totalSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:04.938175+00:00
-- url     : https://prove2.me/theorems/b8e96f57-3576-4bdb-93a6-f243b52e9c91
-- title:
--   Switch: actual total Size
-- statement:
--   The Switch construction uses the actual total Size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L188-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L188-L188

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.actual_totalSize (n : ℕ) : mu n = blockCount (inputBits n) * muZero n := by sorry
