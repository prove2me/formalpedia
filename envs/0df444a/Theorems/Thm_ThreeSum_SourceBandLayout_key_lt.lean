-- Prove2me | Theorems.Thm_ThreeSum_SourceBandLayout_key_lt
-- name    : ThreeSum.SourceBandLayout.key_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:26.877826+00:00
-- url     : https://prove2.me/theorems/bd49fe07-3a0e-4cbf-900e-2cb5f4d37c88
-- title:
--   Source Band Layout: key lt
-- statement:
--   The Source Band Layout construction uses the key lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L122-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean#L122-L123

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets

theorem ThreeSum.SourceBandLayout.key_lt {f : ℕ → ℤ} {g p m : ℕ} {shift : ℤ} (hm : 0 < m) (i j : ℕ) :
    key f g p m shift i j < m := by sorry
