-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairSlices_left_histogram
-- name    : ThreeSum.SourceBandPairSlices.left_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:19.359548+00:00
-- url     : https://prove2.me/theorems/75c97682-e389-404a-9afc-df3ae61dd5b7
-- title:
--   Source Band Pair Slices: left histogram
-- statement:
--   The Source Band Pair Slices construction uses the left histogram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L42-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L42-L50

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData

theorem ThreeSum.SourceBandPairSlices.left_histogram {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m i : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hg : 0 < g) (r : ℕ) (hr : r < m) :
    μ (histLeft base NL NR g m i+r)=
      (LightBlockSourceRetainedStages.histogram p m 0
        (fun j => fL (start g i+j)) (len NL g i) r : ℤ) := by sorry
