-- Prove2me | Theorems.Thm_ThreeSum_SourceBandLayout_work_bound
-- name    : ThreeSum.SourceBandLayout.work_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:05:35.711683+00:00
-- url     : https://prove2.me/theorems/aaa15ead-2296-4469-a839-6384ab6b4a9a
-- title:
--   Source Band Layout: work bound
-- statement:
--   The Source Band Layout construction uses the work bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L79-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L79-L83

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets

theorem ThreeSum.SourceBandLayout.work_bound (base n g m : ℕ) (hg : 0 < g) :
    work base n g m ≤ base+4*n+size n g*(3*m+7) := by sorry
