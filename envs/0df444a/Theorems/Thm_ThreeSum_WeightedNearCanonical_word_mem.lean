-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_word_mem
-- name    : ThreeSum.WeightedNearCanonical.word_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:59.026833+00:00
-- url     : https://prove2.me/theorems/d5789080-2ea2-40a8-8f5c-a44e48fde4d2
-- title:
--   Weighted Near Canonical: word mem
-- statement:
--   The Weighted Near Canonical construction uses the word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L34-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L34-L39

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

theorem ThreeSum.WeightedNearCanonical.word_mem {N D j : ℕ} (Q : TritWord N)
    (hj : j<(WeightedNearEnumeration.words (wordList Q) D).length) :
    word Q D j∈nearWords Q D := by sorry
