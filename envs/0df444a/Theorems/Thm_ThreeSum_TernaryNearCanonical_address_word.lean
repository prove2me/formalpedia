-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_address_word
-- name    : ThreeSum.TernaryNearCanonical.address_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:25.602417+00:00
-- url     : https://prove2.me/theorems/271805b2-e080-4c9e-8b67-74c2e7f88215
-- title:
--   Ternary Near Canonical: address word
-- statement:
--   The Ternary Near Canonical construction uses the address word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L44-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L44-L50

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.address_word {N D j : ℕ} (Q : TritWord N)
    (hj : j<(TernaryNearEnumeration.codes (wordList Q) D).length) :
    address (word Q D j)=(TernaryNearEnumeration.codes (wordList Q) D)[j] := by sorry
