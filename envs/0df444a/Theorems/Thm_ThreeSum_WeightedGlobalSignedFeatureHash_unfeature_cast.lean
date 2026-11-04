-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_unfeature_cast
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.unfeature_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:38:00.917204+00:00
-- url     : https://prove2.me/theorems/ce6b158e-ab18-4f29-a5c4-d34e04da515c
-- title:
--   Weighted Global Signed Feature Hash: unfeature cast
-- statement:
--   The Weighted Global Signed Feature Hash construction uses the unfeature cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L27-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L27-L32

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

theorem ThreeSum.WeightedGlobalSignedFeatureHash.unfeature_cast (raw : Coordinate J→ℤ) :
    unfeature J (fun i => (feature raw i.val : ZMod p))=field raw := by sorry
