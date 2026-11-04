-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_sorted
-- name    : ThreeSum.TernaryNearCanonical.sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:26.035849+00:00
-- url     : https://prove2.me/theorems/12467b5d-976a-41f9-8ab3-eaeb910f6188
-- title:
--   Ternary Near Canonical: sorted
-- statement:
--   The Ternary Near Canonical construction uses the sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L52-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L52-L58

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.sorted {N : ℕ} (Q : TritWord N) (D : ℕ) : ∀ j k, j<k →
    k<(TernaryNearEnumeration.codes (wordList Q) D).length →
    address (word Q D j)<address (word Q D k) := by sorry
