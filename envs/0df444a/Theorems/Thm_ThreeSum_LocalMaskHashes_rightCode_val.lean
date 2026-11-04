-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskHashes_rightCode_val
-- name    : ThreeSum.LocalMaskHashes.rightCode_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:46.518946+00:00
-- url     : https://prove2.me/theorems/68f0c81c-2c5f-4d27-9c5b-b3b0413f6f06
-- title:
--   Local Mask Hashes: right Code val
-- statement:
--   The Local Mask Hashes construction uses the right Code val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L65-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L65-L69

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}

theorem ThreeSum.LocalMaskHashes.rightCode_val (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    rightCode w k i = (HashFamily.hashValue w (LocalGraph.rightWord (setAt L k i))).val := by sorry
