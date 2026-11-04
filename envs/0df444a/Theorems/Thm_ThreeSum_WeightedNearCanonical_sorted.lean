-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_sorted
-- name    : ThreeSum.WeightedNearCanonical.sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:26.3157+00:00
-- url     : https://prove2.me/theorems/e43f5fbb-a8e2-40ea-8dcc-a4866e5f6aa2
-- title:
--   Weighted Near Canonical: sorted
-- statement:
--   The Weighted Near Canonical construction uses the sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L60-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L60-L66

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_WeightedBankCanonical_sorted

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedNearCanonical.sorted {N : ℕ} (Q : TritWord N) (D : ℕ) : ∀ j k, j<k →
    k<(WeightedNearEnumeration.codes (wordList Q) D).length →
    address (word Q D j)<address (word Q D k) := by sorry
