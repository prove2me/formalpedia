-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskHashes_indexed_bucket_count_w3sum_ac885d1
-- name    : ThreeSum.LocalMaskHashes.indexed_bucket_count_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:38.43159+00:00
-- url     : https://prove2.me/theorems/a4ca4d00-4462-4986-864e-6e6a83579422
-- title:
--   Local Mask Hashes: indexed bucket count
-- statement:
--   The Local Mask Hashes construction uses the indexed bucket count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L71-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L71-L101

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}

theorem ThreeSum.LocalMaskHashes.indexed_bucket_count_w3sum_ac885d1 (w : Weight L (LocalField h))
    (shape : Finset (Fin L) → (Fin L → Bool)) (hinj : Function.Injective shape)
    (code : ℕ → ℕ)
    (hcodeLt : ∀ i < LocalMaskGraph.vertexCount L k, code i < localPrime h)
    (hcode : ∀ i < LocalMaskGraph.vertexCount L k,
      (code i : LocalField h) = HashFamily.hashValue w (shape (setAt L k i)))
    {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count code r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize ((LayerCounts.vertices L k).image shape) w (r : LocalField h) := by sorry
