-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedFeatureHash_left_tags
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash.left_tags
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:43:34.401237+00:00
-- url     : https://prove2.me/theorems/cf3e8d75-65c4-4d0a-af8e-2d20a4111135
-- title:
--   left_tags
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L49-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L49-L51

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash.left_tags (U radix J : ℕ) (b : ℤ) :
    feature (leftRaw U radix J b) J=1 ∧ feature (leftRaw U radix J b) (J+1)=0 := by sorry
