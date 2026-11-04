-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskHashes_left_count
-- name    : ThreeSum.LocalMaskHashes.left_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:59.893543+00:00
-- url     : https://prove2.me/theorems/05cabe1d-73ba-4135-ba16-70fa80570a08
-- title:
--   Local Mask Hashes: left count
-- statement:
--   The Local Mask Hashes construction uses the left count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L103-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L103-L107

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}

theorem ThreeSum.LocalMaskHashes.left_count (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (leftCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.leftVertices L k) w (r : LocalField h) := by sorry
