-- Prove2me | Theorems.Thm_ThreeSum_Switch_actual_switch_certified_w3sum_ac885d1
-- name    : ThreeSum.Switch.actual_switch_certified_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:50.009602+00:00
-- url     : https://prove2.me/theorems/7e090588-aedd-40e5-ad0e-448ea464d62e
-- title:
--   Switch: actual switch certified
-- statement:
--   The Switch construction uses the actual switch certified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L219-L241
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L219-L241

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.actual_switch_certified_w3sum_ac885d1 {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    let a : ℝ := (j : ℝ) / blockCount (inputBits n)
    let t : ℝ := (actualSwitch n j : ℝ) / residualSize n j
    t ∈ Icc (0 : ℝ) (1 / 2) ∧
      boxSaving ≤ 2 * bandShift - a + (1 - a) * gamma t ∧
      (1 - a) * entropy t <
        entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu n := by sorry
