-- Prove2me | Theorems.Thm_ThreeSum_SourceBandLayout_start_add_len
-- name    : ThreeSum.SourceBandLayout.start_add_len
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:05:34.229188+00:00
-- url     : https://prove2.me/theorems/3766642b-b427-40a7-9780-18c44e6830cf
-- title:
--   Source Band Layout: start add len
-- statement:
--   The Source Band Layout construction uses the start add len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L35-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L35-L39

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets

theorem ThreeSum.SourceBandLayout.start_add_len {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    start g i+len n g i = stop n g i := by sorry
