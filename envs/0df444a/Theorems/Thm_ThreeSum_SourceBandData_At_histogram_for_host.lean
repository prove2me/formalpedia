-- Prove2me | Theorems.Thm_ThreeSum_SourceBandData_At_histogram_for_host
-- name    : ThreeSum.SourceBandData.At.histogram_for_host
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:05:55.293348+00:00
-- url     : https://prove2.me/theorems/31f1ace2-554a-4423-af74-2fc9f8e1cead
-- title:
--   At: histogram for host
-- statement:
--   The At construction uses the histogram for host property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L79-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L79-L83

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout

theorem ThreeSum.SourceBandData.At.histogram_for_host {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (r : ℕ) (hr : r < m) :
    μ (hist base n g m i+r) =
      (LightBlockSourceRetainedStages.histogram p m shift (fun j => f (start g i+j)) (len n g i) r : ℤ) := by sorry
