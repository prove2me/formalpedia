-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOccurrenceCode_code_step
-- name    : ThreeSum.OutputDecodeOccurrenceCode.code_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:45.131913+00:00
-- url     : https://prove2.me/theorems/72d81581-25ad-4384-bb0c-d6a4b45252cc
-- title:
--   Output Decode Occurrence Code: code step
-- statement:
--   The Output Decode Occurrence Code construction uses the code step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L29-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L29-L37

import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOccurrenceCode
open OutputDecodeOrder OutputDecodeRecords GlobalEncoding
set_option maxHeartbeats 1500000

theorem ThreeSum.OutputDecodeOccurrenceCode.code_step (T M i k : ℕ) :
    code T M (i+1) k = code T M i k+T^i*((k/(T*M)^i)%(T*M)/M) := by sorry
