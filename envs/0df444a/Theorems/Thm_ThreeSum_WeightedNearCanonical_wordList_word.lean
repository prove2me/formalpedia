-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_wordList_word
-- name    : ThreeSum.WeightedNearCanonical.wordList_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:41.594707+00:00
-- url     : https://prove2.me/theorems/701e8580-d4d0-4a25-8109-21a346eb062f
-- title:
--   Weighted Near Canonical: word List word
-- statement:
--   The Weighted Near Canonical construction uses the word List word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L27-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L27-L32

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedNearCanonical.wordList_word {N D j : ℕ} (Q : TritWord N)
    (hj : j<(WeightedNearEnumeration.words (wordList Q) D).length) :
    wordList (word Q D j)=(WeightedNearEnumeration.words (wordList Q) D)[j] := by sorry
