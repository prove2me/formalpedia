-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_complete
-- name    : ThreeSum.WeightedNearCanonical.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:16.869193+00:00
-- url     : https://prove2.me/theorems/0e55b5eb-1920-41ef-9163-675792830087
-- title:
--   Weighted Near Canonical: complete
-- statement:
--   The Weighted Near Canonical construction uses the complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L41-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L41-L48

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedNearCanonical.complete {N D : ℕ} (Q R : TritWord N) (hR : R∈nearWords Q D) :
    ∃ j<(WeightedNearEnumeration.codes (wordList Q) D).length, word Q D j=R := by sorry
