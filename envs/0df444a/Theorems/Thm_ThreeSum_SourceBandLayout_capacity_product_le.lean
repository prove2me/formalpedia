-- Prove2me | Theorems.Thm_ThreeSum_SourceBandLayout_capacity_product_le
-- name    : ThreeSum.SourceBandLayout.capacity_product_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:05:30.445149+00:00
-- url     : https://prove2.me/theorems/ed917253-2583-4ffe-b428-d44db72ba602
-- title:
--   Source Band Layout: capacity product le
-- statement:
--   The Source Band Layout construction uses the capacity product le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L41-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L41-L49

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets

theorem ThreeSum.SourceBandLayout.capacity_product_le (n g : ℕ) (hg : 0 < g) : size n g*cap n g ≤ 2*n := by sorry
