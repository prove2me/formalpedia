-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairSlices_right_histogram
-- name    : ThreeSum.SourceBandPairSlices.right_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:09.032547+00:00
-- url     : https://prove2.me/theorems/f69876bf-2532-4b94-8340-59abe6e5f77e
-- title:
--   Source Band Pair Slices: right histogram
-- statement:
--   The Source Band Pair Slices construction uses the right histogram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L52-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L52-L60

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData

theorem ThreeSum.SourceBandPairSlices.right_histogram {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m i : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hg : 0 < g) (r : ℕ) (hr : r < m) :
    μ (histRight base NL NR g m i+r)=
      (LightBlockSourceRetainedStages.histogram p m shift
        (fun j => fR (start g i+j)) (len NR g i) r : ℤ) := by sorry
