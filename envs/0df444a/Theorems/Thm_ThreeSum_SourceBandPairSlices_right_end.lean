-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairSlices_right_end
-- name    : ThreeSum.SourceBandPairSlices.right_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:10.41103+00:00
-- url     : https://prove2.me/theorems/89daf3be-8237-42a3-ac7f-8d1fe2ad3183
-- title:
--   Source Band Pair Slices: right end
-- statement:
--   The Source Band Pair Slices construction uses the right end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L37-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L37-L40

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData

theorem ThreeSum.SourceBandPairSlices.right_end (base NL NR g m i : ℕ) :
    histRight base NL NR g m i+m ≤ next base NL NR g m := by sorry
