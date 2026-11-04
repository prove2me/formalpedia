-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyOffset_selected_wanted_bound
-- name    : ThreeSum.GlobalKeyOffset.selected_wanted_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:09.481311+00:00
-- url     : https://prove2.me/theorems/6684c005-b8de-48c8-a561-b250c52b216c
-- title:
--   Global Key Offset: selected wanted bound
-- statement:
--   The Global Key Offset construction uses the selected wanted bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L60-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L60-L69

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyOffset.selected_wanted_bound (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) :
    p*wantedCount p left h J (selected p left h J) ≤
      left.length*(scheduleSize h^J*LocalCoverBounds.outputCount (512*h) h^J) := by sorry
