-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_left_tags
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.left_tags
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:42:57.623346+00:00
-- url     : https://prove2.me/theorems/e03dcc33-10bd-45b3-b024-6a8ad03f8a07
-- title:
--   Weighted Global Signed Feature Hash: left tags
-- statement:
--   The Weighted Global Signed Feature Hash construction uses the left tags property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L49-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L49-L51

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

theorem ThreeSum.WeightedGlobalSignedFeatureHash.left_tags (U radix J : ℕ) (b : ℤ) :
    feature (leftRaw U radix J b) J=1 ∧ feature (leftRaw U radix J b) (J+1)=0 := by sorry
