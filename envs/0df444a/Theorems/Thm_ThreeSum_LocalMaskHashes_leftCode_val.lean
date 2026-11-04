-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskHashes_leftCode_val
-- name    : ThreeSum.LocalMaskHashes.leftCode_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:32.513342+00:00
-- url     : https://prove2.me/theorems/70f218e5-bfa7-4990-ab85-261611a9ce29
-- title:
--   Local Mask Hashes: left Code val
-- statement:
--   The Local Mask Hashes construction uses the left Code val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L59-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L59-L63

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}

theorem ThreeSum.LocalMaskHashes.leftCode_val (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    leftCode w k i = (HashFamily.hashValue w (LocalGraph.leftWord (setAt L k i))).val := by sorry
