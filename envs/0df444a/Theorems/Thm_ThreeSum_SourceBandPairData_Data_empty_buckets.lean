-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairData_Data_empty_buckets
-- name    : ThreeSum.SourceBandPairData.Data.empty_buckets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:28.475242+00:00
-- url     : https://prove2.me/theorems/a7ea9018-6e00-43db-9393-3cc26a966b7e
-- title:
--   Data: empty buckets
-- statement:
--   The Data construction uses the empty buckets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L78-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L78-L87

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairData
open Light BandPartition

theorem ThreeSum.SourceBandPairData.Data.empty_buckets {μ : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (key : ℕ → ℕ) :
    SourceBuckets.Stored μ key 0 m (zeroBase base NL NR g m) (next base NL NR g m) := by sorry
