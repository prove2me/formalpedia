-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_canonical_adds
-- name    : ThreeSum.WeightedGlobalRepeatedWords.canonical_adds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:50.414437+00:00
-- url     : https://prove2.me/theorems/e6eccbde-f7aa-4e6f-b142-a04b947f88d8
-- title:
--   Weighted Global Repeated Words: canonical adds
-- statement:
--   The Weighted Global Repeated Words construction uses the canonical adds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L82-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L82-L85

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

theorem ThreeSum.WeightedGlobalRepeatedWords.canonical_adds {r L : ℕ} (a b q : Fin r → TritWord L)
    (h : ∀ i, PointwiseSum (a i) (b i) (q i)) :
    PointwiseSum (canonical a) (canonical b) (canonical q) := by sorry
