-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPartition_source_self
-- name    : ThreeSum.SourceBandPartition.source_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:15.435424+00:00
-- url     : https://prove2.me/theorems/d40b82d7-69fa-41a8-8e4b-dd0c899e7500
-- title:
--   Source Band Partition: source self
-- statement:
--   The Source Band Partition construction uses the source self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L63-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L63-L64

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout

theorem ThreeSum.SourceBandPartition.source_self {n g : ℕ} (hg : 0 < g) (t : Fin n) : t ∈ source n g (t.val/g) := by sorry
