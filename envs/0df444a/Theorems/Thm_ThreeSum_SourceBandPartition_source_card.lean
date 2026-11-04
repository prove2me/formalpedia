-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPartition_source_card
-- name    : ThreeSum.SourceBandPartition.source_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:05:40.166028+00:00
-- url     : https://prove2.me/theorems/e7aa169b-b44c-4267-94e1-1bffe59568b1
-- title:
--   Source Band Partition: source card
-- statement:
--   The Source Band Partition construction uses the source card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L46-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean#L46-L47

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout

theorem ThreeSum.SourceBandPartition.source_card (n g i : ℕ) : (source n g i).card=len n g i := by sorry
