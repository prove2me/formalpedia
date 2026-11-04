-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_right_hash
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.right_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:47:55.135452+00:00
-- url     : https://prove2.me/theorems/19e0db3d-494b-4bcd-8775-36ed07521760
-- title:
--   Weighted Global Signed Feature Hash: right hash
-- statement:
--   The Weighted Global Signed Feature Hash construction uses the right hash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L45-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L45-L47

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedFeatureHash
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalSignedFeatureHash.right_hash (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (U radix : ℕ) (c : ℤ) :
    hash H (fun i => (feature (rightRaw U radix J c) i.val : ZMod p))=sourceRight H U radix c := by sorry
