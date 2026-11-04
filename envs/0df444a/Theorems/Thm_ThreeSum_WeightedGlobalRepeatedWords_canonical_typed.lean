-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_canonical_typed
-- name    : ThreeSum.WeightedGlobalRepeatedWords.canonical_typed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:06.242253+00:00
-- url     : https://prove2.me/theorems/bbf0d851-cbf6-449f-ab8e-7b62ed836dbc
-- title:
--   Weighted Global Repeated Words: canonical typed
-- statement:
--   The Weighted Global Repeated Words construction uses the canonical typed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L78-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L78-L80

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

theorem ThreeSum.WeightedGlobalRepeatedWords.canonical_typed {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) : HasType (canonical blocks) (fun d => r*π d) := by sorry
