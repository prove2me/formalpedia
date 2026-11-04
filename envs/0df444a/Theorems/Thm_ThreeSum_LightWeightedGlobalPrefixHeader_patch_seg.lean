-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_patch_seg
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.patch_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:50:09.600246+00:00
-- url     : https://prove2.me/theorems/ccd1e242-c084-4e7d-987d-e83f3a98a982
-- title:
--   Light Weighted Global Prefix Header: patch seg
-- statement:
--   The Light Weighted Global Prefix Header construction uses the patch seg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L34-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L34-L39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.patch_seg {μ : ℕ→ℤ} {base : ℕ} {xs : List ℤ} (hs : Seg μ base xs)
    (loc : ℕ→ℤ) (fs : List (ℕ×ℕ)) :
    Seg (patch base loc μ fs) base (patchList loc xs fs) := by sorry
