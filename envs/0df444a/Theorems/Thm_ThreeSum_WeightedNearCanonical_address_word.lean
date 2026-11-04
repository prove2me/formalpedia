-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_address_word
-- name    : ThreeSum.WeightedNearCanonical.address_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:12:55.64883+00:00
-- url     : https://prove2.me/theorems/cd8bccca-f0c9-4040-b15c-4c19abdb4c2d
-- title:
--   Weighted Near Canonical: address word
-- statement:
--   The Weighted Near Canonical construction uses the address word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L50-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L50-L58

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_WeightedBankCanonical_address_word

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedNearCanonical.address_word {N D j : ℕ} (Q : TritWord N)
    (hj : j<(WeightedNearEnumeration.codes (wordList Q) D).length) :
    address (word Q D j)=(WeightedNearEnumeration.codes (wordList Q) D)[j] := by sorry
