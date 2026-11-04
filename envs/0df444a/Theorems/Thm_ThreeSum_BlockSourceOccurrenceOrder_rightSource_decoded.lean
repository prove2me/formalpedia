-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_rightSource_decoded
-- name    : ThreeSum.BlockSourceOccurrenceOrder.rightSource_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:43:27.820239+00:00
-- url     : https://prove2.me/theorems/64845d02-27ec-4d96-a713-d7d12d0fe242
-- title:
--   Block Source Occurrence Order: right Source decoded
-- statement:
--   The Block Source Occurrence Order construction uses the right Source decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L50-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L50-L55

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration

theorem ThreeSum.BlockSourceOccurrenceOrder.rightSource_decoded {β : Type*} [Fintype β] [DecidableEq β]
    {h J k : ℕ} (P d : ℤ) (B : Finset β) (b : β → ℤ) (hk : k < localCount h^J) :
    BlockIndexedQuery.rightSource P d B b
      (representative h J (code (scheduleSize h) (layerCount h) J k)) =
    BlockIndexedQuery.rightSource P d B b ((globalRecords h J).getD k (outputDefault h J)) := by sorry
