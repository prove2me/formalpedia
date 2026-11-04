-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_patchList_length
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.patchList_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:49:22.135128+00:00
-- url     : https://prove2.me/theorems/7e89c20f-1b79-467a-b95d-ad5fd8dfc8e1
-- title:
--   Light Weighted Global Prefix Header: patch List length
-- statement:
--   The Light Weighted Global Prefix Header construction uses the patch List length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L18-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L18-L22

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.patchList_length (loc : ℕ→ℤ) (xs : List ℤ) (fs : List (ℕ×ℕ)) :
    (patchList loc xs fs).length=xs.length := by sorry
