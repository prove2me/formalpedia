-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_hash_raw
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.hash_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:42:56.574742+00:00
-- url     : https://prove2.me/theorems/422aa99a-7ad3-4818-9ee6-c35179440557
-- title:
--   Weighted Global Signed Feature Hash: hash raw
-- statement:
--   The Weighted Global Signed Feature Hash construction uses the hash raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L37-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L37-L40

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

theorem ThreeSum.WeightedGlobalSignedFeatureHash.hash_raw (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (raw : Coordinate J→ℤ) :
    hash H (fun i => (feature raw i.val : ZMod p))=H (field raw) := by sorry
