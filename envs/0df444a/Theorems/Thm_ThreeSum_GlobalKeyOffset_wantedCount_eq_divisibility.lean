-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyOffset_wantedCount_eq_divisibility
-- name    : ThreeSum.GlobalKeyOffset.wantedCount_eq_divisibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:51.508673+00:00
-- url     : https://prove2.me/theorems/868df4a1-05d3-4fb4-b3ef-5e8ed5a62920
-- title:
--   Global Key Offset: wanted Count eq divisibility
-- statement:
--   The Global Key Offset construction uses the wanted Count eq divisibility property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L81-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L81-L85

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyOffset.wantedCount_eq_divisibility (p : ℕ) (left : List ℤ) (h J : ℕ) (d : ℤ) :
    wantedCount p left h J d =
      ∑ i : Fin left.length, ∑ q : GlobalOutput h J,
        if (p : ℤ) ∣ left.getD i.val 0+d-globalKey q then 1 else 0 := by sorry
