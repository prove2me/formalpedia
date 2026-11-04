-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_right_tags
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.right_tags
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:44:11.139345+00:00
-- url     : https://prove2.me/theorems/3a14fbb0-6906-43f2-8520-aec7462db28f
-- title:
--   Weighted Global Signed Feature Hash: right tags
-- statement:
--   The Weighted Global Signed Feature Hash construction uses the right tags property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L52-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L52-L54

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

theorem ThreeSum.WeightedGlobalSignedFeatureHash.right_tags (U radix J : ℕ) (c : ℤ) :
    feature (rightRaw U radix J c) J=0 ∧ feature (rightRaw U radix J c) (J+1)=1 := by sorry
