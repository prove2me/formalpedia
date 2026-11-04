-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_outputOccurrences_representative
-- name    : ThreeSum.BlockSourceOccurrenceOrder.outputOccurrences_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:42:44.595113+00:00
-- url     : https://prove2.me/theorems/d14ee6bb-d58c-4083-a829-d9e0646a88c1
-- title:
--   Block Source Occurrence Order: output Occurrences representative
-- statement:
--   The Block Source Occurrence Order construction uses the output Occurrences representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L25-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L25-L26

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration

theorem ThreeSum.BlockSourceOccurrenceOrder.outputOccurrences_representative (h J k : ℕ) :
    outputOccurrences (representative h J k) = occurrences h J k := by sorry

attribute [defeq] ThreeSum.BlockSourceOccurrenceOrder.outputOccurrences_representative
