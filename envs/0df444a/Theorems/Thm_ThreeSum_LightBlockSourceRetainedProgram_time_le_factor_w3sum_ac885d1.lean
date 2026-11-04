-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceRetainedProgram_time_le_factor_w3sum_ac885d1
-- name    : ThreeSum.LightBlockSourceRetainedProgram.time_le_factor_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:38.314194+00:00
-- url     : https://prove2.me/theorems/57948584-71f1-4314-8213-08d15ae1742f
-- title:
--   Light Block Source Retained Program: time le factor
-- statement:
--   The Light Block Source Retained Program construction uses the time le factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedProgram.lean#L67-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedProgram.lean#L67-L79

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedProgram
open Light LightPascal LightSubsetAddress LightBlockSourceRetainedHost
open LocalCoverBounds SubsetAddress BlockSourceEncoding LightBlockSourceBuild
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

theorem ThreeSum.LightBlockSourceRetainedProgram.time_le_factor_w3sum_ac885d1 {h J cut : ℕ} (hcut : cut ≤ J*(512*h)) :
    LightBlockSourceRetainedHost.time h J cut ≤ factor h J*(downsetCap (J*(512*h)) cut+1) := by sorry
