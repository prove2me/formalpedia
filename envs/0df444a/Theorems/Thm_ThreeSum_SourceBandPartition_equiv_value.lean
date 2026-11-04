-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPartition_equiv_value
-- name    : ThreeSum.SourceBandPartition.equiv_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:19.349002+00:00
-- url     : https://prove2.me/theorems/e0b56e13-f218-4ef0-a4ad-ea9936ba7445
-- title:
--   Source Band Partition: equiv value
-- statement:
--   The Source Band Partition construction uses the equiv value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L43-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L43-L44

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout

theorem ThreeSum.SourceBandPartition.equiv_value {n g i : ℕ} (f : ℕ → ℤ) (j : Fin (len n g i)) :
    f (start g i+j.val) = f ((equiv n g i j).val.val) := by sorry
