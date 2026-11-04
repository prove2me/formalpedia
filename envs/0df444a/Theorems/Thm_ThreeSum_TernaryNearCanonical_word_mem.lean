-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_word_mem
-- name    : ThreeSum.TernaryNearCanonical.word_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:45.704724+00:00
-- url     : https://prove2.me/theorems/c4408c3e-1855-48d3-91b7-3cf3ac679eed
-- title:
--   Ternary Near Canonical: word mem
-- statement:
--   The Ternary Near Canonical construction uses the word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L28-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L28-L33

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.word_mem {N D j : ℕ} (Q : TritWord N)
    (hj : j<(TernaryNearEnumeration.words (wordList Q) D).length) :
    word Q D j∈nearWords Q D := by sorry
