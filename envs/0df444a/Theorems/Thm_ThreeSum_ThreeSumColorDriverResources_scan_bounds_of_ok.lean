-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumColorDriverResources_scan_bounds_of_ok
-- name    : ThreeSum.ThreeSumColorDriverResources.scan_bounds_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:14:41.865209+00:00
-- url     : https://prove2.me/theorems/e12fcad9-b677-4367-8a29-d92cd2976908
-- title:
--   Three Sum Color Driver Resources: scan bounds of ok
-- statement:
--   The Three Sum Color Driver Resources construction uses the scan bounds of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L32-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L32-L40

import Definitions.Def_Submission_ThreeSum_LightThreeSumColorDriver
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Theorems.Thm_ThreeSum_SharedReportingBankHeader_Stored_row

set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumColorDriverResources
open Light Scales StageBounds ArithmeticStageBounds LightColorParametersCosts ColorParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

theorem ThreeSum.ThreeSumColorDriverResources.scan_bounds_of_ok {lim : Limits} {colorNeed : ℕ→ℕ→Need} {n U row d : ℕ}
    (H : (need colorNeed n U).Ok lim row d) :
    row+6≤lim.space ∧ (LightColorScanHost.word n : ℤ)≤lim.word ∧
      d+count (width n)+(colorNeed n U).depth+4≤lim.depth := by sorry
