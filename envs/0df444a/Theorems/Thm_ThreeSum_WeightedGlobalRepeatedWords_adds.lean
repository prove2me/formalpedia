-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_adds
-- name    : ThreeSum.WeightedGlobalRepeatedWords.adds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:21.99465+00:00
-- url     : https://prove2.me/theorems/7fd9924a-8ada-474b-8d39-01490bac6fec
-- title:
--   Weighted Global Repeated Words: adds
-- statement:
--   The Weighted Global Repeated Words construction uses the adds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L37-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L37-L40

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

theorem ThreeSum.WeightedGlobalRepeatedWords.adds {r L : ℕ} (a b q : Fin r → TritWord L)
    (h : ∀ i, PointwiseSum (a i) (b i) (q i)) : PointwiseSum (word a) (word b) (word q) := by sorry
