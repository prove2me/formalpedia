-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_wordList_word
-- name    : ThreeSum.TernaryNearCanonical.wordList_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:50.825052+00:00
-- url     : https://prove2.me/theorems/f0863711-693a-4206-99ce-3451221327e6
-- title:
--   Ternary Near Canonical: word List word
-- statement:
--   The Ternary Near Canonical construction uses the word List word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L21-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L21-L26

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.wordList_word {N D j : ℕ} (Q : TritWord N)
    (hj : j<(TernaryNearEnumeration.words (wordList Q) D).length) :
    wordList (word Q D j)=(TernaryNearEnumeration.words (wordList Q) D)[j] := by sorry
