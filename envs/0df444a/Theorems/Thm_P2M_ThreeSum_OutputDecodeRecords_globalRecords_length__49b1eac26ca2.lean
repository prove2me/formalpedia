-- Prove2me | Theorems.Thm_P2M_ThreeSum_OutputDecodeRecords_globalRecords_length__49b1eac26ca2
-- name    : P2M_ThreeSum_OutputDecodeRecords_globalRecords_length__49b1eac26ca2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:24.842047+00:00
-- url     : https://prove2.me/theorems/95c8ce39-a652-4d86-99be-4aec40668be9
-- title:
--   P2 M Three Sum Output Decode Records global Records length  49b1eac26ca2: P2 M Three Sum Output Decode Records global Records length  49b1eac26ca2
-- statement:
--   The P2 M Three Sum Output Decode Records global Records length  49b1eac26ca2 construction uses the P2 M Three Sum Output Decode Records global Records length  49b1eac26ca2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L70-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L70-L72

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem P2M_ThreeSum_OutputDecodeRecords_globalRecords_length__49b1eac26ca2 (h J : ℕ) : (globalRecords h J).length=localCount h^J := by sorry

alias «ThreeSum».«OutputDecodeRecords».«globalRecords_length'» := P2M_ThreeSum_OutputDecodeRecords_globalRecords_length__49b1eac26ca2
