-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_row_coordinate
-- name    : ThreeSum.BlockSourceOccurrenceOrder.row_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:42:55.845345+00:00
-- url     : https://prove2.me/theorems/f9173404-efaa-4327-8770-a90df196421b
-- title:
--   Block Source Occurrence Order: row coordinate
-- statement:
--   The Block Source Occurrence Order construction uses the row coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L28-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L28-L32

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration

theorem ThreeSum.BlockSourceOccurrenceOrder.row_coordinate {h J k j : ℕ} (hj : j < J) :
    occurrenceIndices (outputOccurrences (representative h J k)) j =
      (indices (scheduleSize h) J k).getD j 0 := by sorry
