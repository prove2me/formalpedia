-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOccurrenceCode_code_indices
-- name    : ThreeSum.OutputDecodeOccurrenceCode.code_indices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:07.196963+00:00
-- url     : https://prove2.me/theorems/b4140118-2879-4a0f-a4bc-d0abc1c1dd1c
-- title:
--   Output Decode Occurrence Code: code indices
-- statement:
--   The Output Decode Occurrence Code construction uses the code indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L39-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L39-L54

import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOccurrenceCode
open OutputDecodeOrder OutputDecodeRecords GlobalEncoding
set_option maxHeartbeats 1500000

theorem ThreeSum.OutputDecodeOccurrenceCode.code_indices {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) :
    indices T J (code T M J k) = (indices (T*M) J k).map (fun i => i/M) := by sorry
