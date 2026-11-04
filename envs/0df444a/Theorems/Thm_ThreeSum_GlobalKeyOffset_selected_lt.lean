-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyOffset_selected_lt
-- name    : ThreeSum.GlobalKeyOffset.selected_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:38.149361+00:00
-- url     : https://prove2.me/theorems/5d610985-9fdd-49db-a0a8-5bbcf52e36a4
-- title:
--   Global Key Offset: selected lt
-- statement:
--   The Global Key Offset construction uses the selected lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L57-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L57-L58

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Theorems.Thm_ThreeSum_LightOriginalOffset_selected_lt

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyOffset.selected_lt (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) :
    selected p left h J < p := by sorry
