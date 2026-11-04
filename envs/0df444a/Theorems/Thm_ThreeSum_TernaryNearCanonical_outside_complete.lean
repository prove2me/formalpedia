-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_outside_complete
-- name    : ThreeSum.TernaryNearCanonical.outside_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:12:05.376188+00:00
-- url     : https://prove2.me/theorems/28855b73-c71a-44bc-8be4-6175f219c506
-- title:
--   Ternary Near Canonical: outside complete
-- statement:
--   Every outside-bank descendant required by Euler or inversion is emitted.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L87-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L87-L91

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.outside_complete {N T : ℕ} (Q R : TritWord N) (hQ : T<rank Q)
    (hRQ : Below R Q) (hR : T<rank R) :
    ∃ j<(TernaryNearEnumeration.codes (wordList Q) (rank Q-(T+1))).length,
      word Q (rank Q-(T+1)) j=R := by sorry
