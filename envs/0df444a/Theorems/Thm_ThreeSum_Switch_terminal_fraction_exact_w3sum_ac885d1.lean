-- Prove2me | Theorems.Thm_ThreeSum_Switch_terminal_fraction_exact_w3sum_ac885d1
-- name    : ThreeSum.Switch.terminal_fraction_exact_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:52.221918+00:00
-- url     : https://prove2.me/theorems/079efcf6-9a7b-4664-9240-3104d7b94d16
-- title:
--   Switch: terminal fraction exact
-- statement:
--   The Switch construction uses the terminal fraction exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L243-L256
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L243-L256

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section

theorem ThreeSum.Switch.terminal_fraction_exact_w3sum_ac885d1 {n : ℕ} (hmu : 0 < mu n) :
    (terminalDepth n : ℝ) / blockCount (inputBits n) = terminalFraction := by sorry
