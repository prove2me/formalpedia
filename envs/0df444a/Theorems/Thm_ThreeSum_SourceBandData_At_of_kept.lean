-- Prove2me | Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
-- name    : ThreeSum.SourceBandData.At.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:56:25.267064+00:00
-- url     : https://prove2.me/theorems/7636f4ac-9563-40ae-8c33-cf7637837332
-- title:
--   At: of kept
-- statement:
--   The At construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L64-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L64-L77

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout

theorem ThreeSum.SourceBandData.At.of_kept {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i bound : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m) (hi : i < size n g)
    (K : Kept μ ν bound) (hbound : work base n g m ≤ bound) :
    At ν f base n g p m shift i := by sorry
