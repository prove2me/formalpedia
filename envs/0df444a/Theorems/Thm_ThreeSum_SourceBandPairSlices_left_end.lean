-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairSlices_left_end
-- name    : ThreeSum.SourceBandPairSlices.left_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:06.49669+00:00
-- url     : https://prove2.me/theorems/320c6044-7efb-4615-be28-17611852ace9
-- title:
--   Source Band Pair Slices: left end
-- statement:
--   The Source Band Pair Slices construction uses the left end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L31-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L31-L35

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData

theorem ThreeSum.SourceBandPairSlices.left_end (base NL NR g m i : ℕ) :
    histLeft base NL NR g m i+m ≤ next base NL NR g m := by sorry
