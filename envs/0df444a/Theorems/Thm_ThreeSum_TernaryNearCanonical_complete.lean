-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
-- name    : ThreeSum.TernaryNearCanonical.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:19.648016+00:00
-- url     : https://prove2.me/theorems/f800603a-deac-46b2-ab16-17a20fd16e8c
-- title:
--   Ternary Near Canonical: complete
-- statement:
--   The Ternary Near Canonical construction uses the complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L35-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L35-L42

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.complete {N D : ℕ} (Q R : TritWord N) (hR : R∈nearWords Q D) :
    ∃ j<(TernaryNearEnumeration.codes (wordList Q) D).length, word Q D j=R := by sorry
