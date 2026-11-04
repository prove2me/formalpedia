-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_scan_ok
-- name    : ThreeSum.WeightedGlobalFastProgramResources.scan_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:56:56.0765+00:00
-- url     : https://prove2.me/theorems/c3eb0fa6-06a8-4885-a993-33a08638fe8b
-- title:
--   Weighted Global Fast Program Resources: scan ok
-- statement:
--   The Weighted Global Fast Program Resources construction uses the scan ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L35-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L35-L41

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

theorem ThreeSum.WeightedGlobalFastProgramResources.scan_ok {M b p K κ n U free depth : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth) :
    (ThreeSumColorDriverResources.need colorNeed n U).Ok lim
      (scanFree M b p K κ n free) (depth+1) := by sorry
