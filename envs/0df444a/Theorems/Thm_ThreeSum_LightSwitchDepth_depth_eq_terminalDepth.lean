-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchDepth_depth_eq_terminalDepth
-- name    : ThreeSum.LightSwitchDepth.depth_eq_terminalDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:41.930808+00:00
-- url     : https://prove2.me/theorems/25b47b16-af39-4718-a5b2-a80af2819a2d
-- title:
--   Light Switch Depth: depth eq terminal Depth
-- statement:
--   The Light Switch Depth construction uses the depth eq terminal Depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchDepth.lean#L40-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchDepth.lean#L40-L41

import Definitions.Def_Submission_ThreeSum_LightSwitch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchDepth
open Light
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}

theorem ThreeSum.LightSwitchDepth.depth_eq_terminalDepth (n : ℕ) :
    depth (Scales.blockCount (Scales.inputBits n))=Switch.terminalDepth n := by sorry
