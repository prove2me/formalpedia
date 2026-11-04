-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_canonical_wordList
-- name    : ThreeSum.WeightedGlobalRepeatedWords.canonical_wordList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:32.397334+00:00
-- url     : https://prove2.me/theorems/7b5e0adb-64be-4aa1-ab8d-b68bc997025e
-- title:
--   Weighted Global Repeated Words: canonical word List
-- statement:
--   The Weighted Global Repeated Words construction uses the canonical word List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L71-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L71-L76

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRepeatedWords
open TernaryJointType Finset
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalRepeatedWords.canonical_wordList {r L : ℕ} (blocks : Fin r → TritWord L) :
    TernaryBankEnumeration.wordList (canonical blocks)=
      (List.ofFn blocks).reverse.flatMap TernaryBankEnumeration.wordList := by sorry
