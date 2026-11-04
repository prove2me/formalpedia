-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_read_of_seg
-- name    : ThreeSum.WeightedNearCanonical.read_of_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:21.522204+00:00
-- url     : https://prove2.me/theorems/c4f5b207-78c5-4d91-a6fa-fecde72ba491
-- title:
--   Weighted Near Canonical: read of seg
-- statement:
--   The Weighted Near Canonical construction uses the read of seg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L68-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L68-L74

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_WeightedBankCanonical_read_of_seg

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedNearCanonical.read_of_seg {N D a : ℕ} (Q : TritWord N) (μ : ℕ → ℤ)
    (hseg : Light.Seg μ a ((WeightedNearEnumeration.codes (wordList Q) D).map (fun c => (c : ℤ)))) :
    ∀ j<(WeightedNearEnumeration.codes (wordList Q) D).length,
      μ (a+j)=(address (word Q D j) : ℤ) := by sorry
