-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_scan_bounds
-- name    : ThreeSum.WeightedGlobalFastProgramResources.scan_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:58:33.544738+00:00
-- url     : https://prove2.me/theorems/b1949416-7e7c-47d7-ba6c-44a86eef771c
-- title:
--   Weighted Global Fast Program Resources: scan bounds
-- statement:
--   The Weighted Global Fast Program Resources construction uses the scan bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L49-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L49-L55

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalFastProgramResources.scan_bounds {M b p K κ n U free depth : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth) :
    scanFree M b p K κ n free+6≤lim.space ∧
    (LightColorScanHost.word n : ℤ)≤lim.word ∧
    depth+ColorParameters.count (LightColorParametersCosts.width n)+(colorNeed n U).depth+5≤lim.depth := by sorry
