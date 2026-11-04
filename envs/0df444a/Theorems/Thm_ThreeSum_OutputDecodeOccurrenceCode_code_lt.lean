-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOccurrenceCode_code_lt
-- name    : ThreeSum.OutputDecodeOccurrenceCode.code_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:47.328583+00:00
-- url     : https://prove2.me/theorems/2f286c2b-1d2b-4d6c-8b36-6e118b28d298
-- title:
--   Output Decode Occurrence Code: code lt
-- statement:
--   The Output Decode Occurrence Code construction uses the code lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L19-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L19-L27

import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOccurrenceCode
open OutputDecodeOrder OutputDecodeRecords GlobalEncoding
set_option maxHeartbeats 1500000

theorem ThreeSum.OutputDecodeOccurrenceCode.code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : code T M J k < T^J := by sorry
