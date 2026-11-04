-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_index_not_deleted
-- name    : ThreeSum.WeightedGlobalCompactPairedSupport.index_not_deleted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:07:18.858428+00:00
-- url     : https://prove2.me/theorems/72ffc148-5606-460d-81ce-8dea9160b986
-- title:
--   Weighted Global Compact Paired Support: index not deleted
-- statement:
--   The Weighted Global Compact Paired Support construction uses the index not deleted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L20-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L20-L37

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCompactPairedSupport
open LightOriginalSurvivors LightOriginalCollisionCleanup LightOriginalBucketFilter
open TernaryPairedSupportConcrete TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalCompactPairedSupport.index_not_deleted {W : Type*} [DecidableEq W] {keys : ℕ → ℕ} {n j : ℕ}
    (hash : Fin n → W) (hj : j < (indices keys n).length)
    (heq : ∀ a b : Fin n, hash a = hash b → keys a.val = keys b.val) :
    (⟨index keys n j,index_lt hj⟩ : Fin n) ∉ TernaryOriginalCollisions.deleted hash := by sorry
