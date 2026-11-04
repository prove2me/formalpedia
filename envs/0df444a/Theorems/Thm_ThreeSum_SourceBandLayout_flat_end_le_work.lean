-- Prove2me | Theorems.Thm_ThreeSum_SourceBandLayout_flat_end_le_work
-- name    : ThreeSum.SourceBandLayout.flat_end_le_work
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:20.845513+00:00
-- url     : https://prove2.me/theorems/3be8f3f6-1192-4b0d-8d05-602be6690d24
-- title:
--   Source Band Layout: flat end le work
-- statement:
--   The Source Band Layout construction uses the flat end le work property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L69-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L69-L72

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets

theorem ThreeSum.SourceBandLayout.flat_end_le_work {base n g m i : ℕ} (hi : i < size n g) :
    flat base n g m i+cap n g ≤ work base n g m := by sorry
