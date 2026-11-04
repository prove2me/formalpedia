-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskHashes_leftCode_cast
-- name    : ThreeSum.LocalMaskHashes.leftCode_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:25.180486+00:00
-- url     : https://prove2.me/theorems/642976a4-5404-4722-8506-34637ed136f3
-- title:
--   Local Mask Hashes: left Code cast
-- statement:
--   The Local Mask Hashes construction uses the left Code cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L43-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L43-L49

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}

theorem ThreeSum.LocalMaskHashes.leftCode_cast (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (leftCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.leftWord (setAt L k i)) := by sorry
