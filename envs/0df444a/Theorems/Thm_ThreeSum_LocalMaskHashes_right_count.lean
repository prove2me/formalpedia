-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskHashes_right_count
-- name    : ThreeSum.LocalMaskHashes.right_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:41.403072+00:00
-- url     : https://prove2.me/theorems/a0bff0d9-4160-47e5-a685-bf01d3959256
-- title:
--   Local Mask Hashes: right count
-- statement:
--   The Local Mask Hashes construction uses the right count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L109-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L109-L113

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}

theorem ThreeSum.LocalMaskHashes.right_count (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (rightCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.rightVertices L k) w (r : LocalField h) := by sorry
