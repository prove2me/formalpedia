-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_left_hash
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.left_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:43:38.902197+00:00
-- url     : https://prove2.me/theorems/7a2d66a2-2922-4e70-941a-f3b602b6024f
-- title:
--   Weighted Global Signed Feature Hash: left hash
-- statement:
--   The Weighted Global Signed Feature Hash construction uses the left hash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L42-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L42-L44

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

theorem ThreeSum.WeightedGlobalSignedFeatureHash.left_hash (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (U radix : ℕ) (b : ℤ) :
    hash H (fun i => (feature (leftRaw U radix J b) i.val : ZMod p))=sourceLeft H U radix b := by sorry
