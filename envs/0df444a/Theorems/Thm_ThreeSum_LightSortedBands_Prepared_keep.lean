-- Prove2me | Theorems.Thm_ThreeSum_LightSortedBands_Prepared_keep
-- name    : ThreeSum.LightSortedBands.Prepared.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:43:05.122145+00:00
-- url     : https://prove2.me/theorems/e5145fd2-1656-4bf1-b806-b01c1c86ad16
-- title:
--   Prepared: keep
-- statement:
--   The Prepared construction uses the keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L205-L211
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L205-L211

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSortedBands.Prepared.keep {μ μ' : ℕ → ℤ} {values endpoints g bound : ℕ}
    {original : List ℤ} (h : Prepared μ values endpoints g original)
    (hk : Kept μ μ' bound) (hv : values+original.length ≤ bound)
    (he : endpoints+2+2*original.length ≤ bound) : Prepared μ' values endpoints g original := by sorry
