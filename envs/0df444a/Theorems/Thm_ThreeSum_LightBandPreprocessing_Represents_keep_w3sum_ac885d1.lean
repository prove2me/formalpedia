-- Prove2me | Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_keep_w3sum_ac885d1
-- name    : ThreeSum.LightBandPreprocessing.Represents.keep_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:57.223783+00:00
-- url     : https://prove2.me/theorems/871ff0d5-12c8-4c8f-a4ca-cb982d99e801
-- title:
--   Represents: keep
-- statement:
--   The Represents construction uses the keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPreprocessing.lean#L41-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPreprocessing.lean#L41-L57

import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_keep

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandPreprocessing.Represents.keep_w3sum_ac885d1 {μ μ' : ℕ → ℤ} {values endpoints g bound : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (h : Represents μ values endpoints g hg original L hs) (hk : Kept μ μ' bound)
    (hv : values+original.length ≤ bound) (he : endpoints+2+2*original.length ≤ bound) :
    Represents μ' values endpoints g hg original L hs := by sorry
