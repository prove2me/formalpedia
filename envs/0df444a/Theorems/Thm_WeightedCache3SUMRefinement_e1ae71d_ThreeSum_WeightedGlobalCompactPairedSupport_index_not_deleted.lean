-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCompactPairedSupport_index_not_deleted
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCompactPairedSupport.index_not_deleted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:21:01.391657+00:00
-- url     : https://prove2.me/theorems/0b7b2eea-1cb7-4a48-8cd5-d633cf39b251
-- title:
--   index_not_deleted
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L20-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L20-L37

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedSelectedChain
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCompactPairedSupport
open LightOriginalSurvivors LightOriginalCollisionCleanup LightOriginalBucketFilter
open TernaryPairedSupportConcrete TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCompactPairedSupport.index_not_deleted {W : Type*} [DecidableEq W] {keys : ℕ → ℕ} {n j : ℕ}
    (hash : Fin n → W) (hj : j < (indices keys n).length)
    (heq : ∀ a b : Fin n, hash a = hash b → keys a.val = keys b.val) :
    (⟨index keys n j,index_lt hj⟩ : Fin n) ∉ TernaryOriginalCollisions.deleted hash := by sorry
