-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPartition_source_eq_empty
-- name    : ThreeSum.SourceBandPartition.source_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:10.025991+00:00
-- url     : https://prove2.me/theorems/19bf4552-6742-4ad4-930c-743db33896dd
-- title:
--   Source Band Partition: source eq empty
-- statement:
--   The Source Band Partition construction uses the source eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L59-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L59-L61

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout

theorem ThreeSum.SourceBandPartition.source_eq_empty {n g i : ℕ} (hg : 0 < g) (hi : size n g ≤ i) : source n g i=∅ := by sorry
