-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalTupleCodes_word_tuple_code
-- name    : ThreeSum.WeightedGlobalCanonicalTupleCodes.word_tuple_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:12:15.780688+00:00
-- url     : https://prove2.me/theorems/204703b0-cacd-4dc7-834c-4e09caf79c29
-- title:
--   Weighted Global Canonical Tuple Codes: word tuple code
-- statement:
--   The Weighted Global Canonical Tuple Codes construction uses the word tuple code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L16-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L16-L26

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleWantedLookup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalTupleCodes
open TernaryJointType
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalCanonicalTupleCodes.word_tuple_code {A : Type*} {L : ℕ} (word : A→TritWord L) (xs : List A) :
    Radix.positionalHash ((4^L : ℕ) : ℤ)
      (fun a => (TernaryCodeSemantics.address (word a) : ℤ)) xs=
      (TernaryAddresses.code (xs.reverse.flatMap (TernaryBankEnumeration.wordList ∘ word)) : ℤ) := by sorry
