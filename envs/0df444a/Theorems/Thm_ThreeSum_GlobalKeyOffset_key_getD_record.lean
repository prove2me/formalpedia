-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyOffset_key_getD_record
-- name    : ThreeSum.GlobalKeyOffset.key_getD_record
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:48.056895+00:00
-- url     : https://prove2.me/theorems/4ad12fa4-b6c7-4551-8ff4-5715a2efc83f
-- title:
--   Global Key Offset: key get D record
-- statement:
--   The Global Key Offset construction uses the key get D record property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L27-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L27-L31

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyOffset.key_getD_record (h J : ℕ) (i : Fin (globalRecords h J).length) :
    (globalKeys h J).getD i.val 0=globalKey (recordEquiv h J i) := by sorry
