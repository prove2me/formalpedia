-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyOffset_residue_relation_iff
-- name    : ThreeSum.GlobalKeyOffset.residue_relation_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:44.034163+00:00
-- url     : https://prove2.me/theorems/80324526-c588-4919-a44f-dcac5550d721
-- title:
--   Global Key Offset: residue relation iff
-- statement:
--   The Global Key Offset construction uses the residue relation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L71-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L71-L79

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyOffset.residue_relation_iff (p : ℕ) (left right d : ℤ) :
    (right : ZMod p)-(left : ZMod p)=(d : ZMod p) ↔ (p : ℤ) ∣ left+d-right := by sorry
