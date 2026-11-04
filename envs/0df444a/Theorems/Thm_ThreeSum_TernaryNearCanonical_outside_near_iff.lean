-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_outside_near_iff
-- name    : ThreeSum.TernaryNearCanonical.outside_near_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:30.111405+00:00
-- url     : https://prove2.me/theorems/4fcbcb98-f7d9-4814-adc4-320b4a42a367
-- title:
--   Ternary Near Canonical: outside near iff
-- statement:
--   The Ternary Near Canonical construction uses the outside near iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L68-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L68-L77

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.outside_near_iff {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<rank Q) :
    R∈nearWords Q (rank Q-(T+1)) ↔ Below R Q ∧ T<rank R := by sorry
