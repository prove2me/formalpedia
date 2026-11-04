-- Prove2me | Theorems.Thm_ThreeSum_BandPartition_index_lt_size
-- name    : ThreeSum.BandPartition.index_lt_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:29.621073+00:00
-- url     : https://prove2.me/theorems/7523e5ff-5ecd-40ce-b988-b0b8a7493507
-- title:
--   Band Partition: index lt size
-- statement:
--   The Band Partition construction uses the index lt size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPartition.lean#L70-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPartition.lean#L70-L74

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition

theorem ThreeSum.BandPartition.index_lt_size {n g i : ℕ} (hi : i < n) : i/g < size n g := by sorry
