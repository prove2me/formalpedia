-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOccurrenceCode_source_code_coordinate
-- name    : ThreeSum.OutputDecodeOccurrenceCode.source_code_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:50.437396+00:00
-- url     : https://prove2.me/theorems/d0ec55df-3333-48ac-bff5-5def9c64f134
-- title:
--   Output Decode Occurrence Code: source code coordinate
-- statement:
--   The Output Decode Occurrence Code construction uses the source code coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L60-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L60-L68

import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOccurrenceCode
open OutputDecodeOrder OutputDecodeRecords GlobalEncoding
set_option maxHeartbeats 1500000

theorem ThreeSum.OutputDecodeOccurrenceCode.source_code_coordinate (h J k : ℕ) {j : ℕ} (hj : j < J) :
    (indices (scheduleSize h) J (code (scheduleSize h) (layerCount h) J k)).getD j 0 =
      occurrenceIndex h J k j := by sorry
