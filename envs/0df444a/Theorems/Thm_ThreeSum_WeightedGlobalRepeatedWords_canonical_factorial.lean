-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_canonical_factorial
-- name    : ThreeSum.WeightedGlobalRepeatedWords.canonical_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:38.876433+00:00
-- url     : https://prove2.me/theorems/318c94cf-7519-4ddc-b448-95c27cf0b184
-- title:
--   Weighted Global Repeated Words: canonical factorial
-- statement:
--   The Weighted Global Repeated Words construction uses the canonical factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L87-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L87-L90

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

theorem ThreeSum.WeightedGlobalRepeatedWords.canonical_factorial {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) :
    TernaryConvolution.factorial (canonical blocks)=(2 : ℤ)^(r*π 2) := by sorry
