-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_leftSource_decoded
-- name    : ThreeSum.BlockSourceOccurrenceOrder.leftSource_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:43:23.206288+00:00
-- url     : https://prove2.me/theorems/f455b420-1725-439c-b2b3-90a109d5e96e
-- title:
--   Block Source Occurrence Order: left Source decoded
-- statement:
--   The Block Source Occurrence Order construction uses the left Source decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L43-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L43-L48

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration

theorem ThreeSum.BlockSourceOccurrenceOrder.leftSource_decoded {β : Type*} [Fintype β] [DecidableEq β]
    {h J k : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (hk : k < localCount h^J) :
    BlockIndexedQuery.leftSource P B b
      (representative h J (code (scheduleSize h) (layerCount h) J k)) =
    BlockIndexedQuery.leftSource P B b ((globalRecords h J).getD k (outputDefault h J)) := by sorry
