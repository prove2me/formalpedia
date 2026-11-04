-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPartition_source_unique
-- name    : ThreeSum.SourceBandPartition.source_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:17.578835+00:00
-- url     : https://prove2.me/theorems/08f139e2-5215-48a0-8e20-651c2fb328c1
-- title:
--   Source Band Partition: source unique
-- statement:
--   The Source Band Partition construction uses the source unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L66-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L66-L79

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout

theorem ThreeSum.SourceBandPartition.source_unique {n g i j : ℕ} {t : Fin n}
    (hi : t ∈ source n g i) (hj : t ∈ source n g j) : i=j := by sorry
