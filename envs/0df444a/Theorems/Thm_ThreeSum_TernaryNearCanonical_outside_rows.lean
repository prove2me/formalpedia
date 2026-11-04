-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_outside_rows
-- name    : ThreeSum.TernaryNearCanonical.outside_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:33.896645+00:00
-- url     : https://prove2.me/theorems/78be886f-8b3d-48ec-a71e-4806f98931dd
-- title:
--   Ternary Near Canonical: outside rows
-- statement:
--   With the exact cutoff, every emitted row lies outside the stored bank.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L80-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L80-L84

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.outside_rows {N j T : ℕ} (Q : TritWord N) (hQ : T<rank Q)
    (hj : j<(TernaryNearEnumeration.codes (wordList Q) (rank Q-(T+1))).length) :
    Below (word Q (rank Q-(T+1)) j) Q ∧ T<rank (word Q (rank Q-(T+1)) j) := by sorry
