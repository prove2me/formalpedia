-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_decoded_occurrences
-- name    : ThreeSum.BlockSourceOccurrenceOrder.decoded_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:42:44.308681+00:00
-- url     : https://prove2.me/theorems/d12c92d8-3058-49dc-9cfe-9074985958c1
-- title:
--   Block Source Occurrence Order: decoded occurrences
-- statement:
--   The Block Source Occurrence Order construction uses the decoded occurrences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L34-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L34-L41

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration

theorem ThreeSum.BlockSourceOccurrenceOrder.decoded_occurrences {h J k : ℕ} (hk : k < localCount h^J) :
    outputOccurrences (representative h J (code (scheduleSize h) (layerCount h) J k)) =
      outputOccurrences ((globalRecords h J).getD k (outputDefault h J)) := by sorry
