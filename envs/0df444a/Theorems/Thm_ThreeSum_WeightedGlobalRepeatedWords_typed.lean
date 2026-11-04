-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_typed
-- name    : ThreeSum.WeightedGlobalRepeatedWords.typed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:49.43853+00:00
-- url     : https://prove2.me/theorems/0abf531a-925c-4f34-8a3b-fb92c7eacee0
-- title:
--   Weighted Global Repeated Words: typed
-- statement:
--   The Weighted Global Repeated Words construction uses the typed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L25-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L25-L35

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

theorem ThreeSum.WeightedGlobalRepeatedWords.typed {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) : HasType (word blocks) (fun d => r*π d) := by sorry
