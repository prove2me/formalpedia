-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorNormalizedData_records_length_le
-- name    : ThreeSum.EncodedColorNormalizedData.records_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:39:23.346197+00:00
-- url     : https://prove2.me/theorems/d18fa2bc-a67e-404a-bcc0-045611ccd7c1
-- title:
--   Encoded Color Normalized Data: records length le
-- statement:
--   The Encoded Color Normalized Data construction uses the records length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorNormalizedData.lean#L26-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorNormalizedData.lean#L26-L36

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_EncodedColorParameterData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorNormalizedData
open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout

theorem ThreeSum.EncodedColorNormalizedData.records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (sortedRecords A B C g hg hsA hsB hsC).length ≤ ColorBandBounds.count n g := by sorry
