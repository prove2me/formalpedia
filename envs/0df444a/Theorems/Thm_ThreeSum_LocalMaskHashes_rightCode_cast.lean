-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskHashes_rightCode_cast
-- name    : ThreeSum.LocalMaskHashes.rightCode_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:09.038686+00:00
-- url     : https://prove2.me/theorems/5b6ded6c-f53f-4df5-be88-7a1313d80ff9
-- title:
--   Local Mask Hashes: right Code cast
-- statement:
--   The Local Mask Hashes construction uses the right Code cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L51-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean#L51-L57

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}

theorem ThreeSum.LocalMaskHashes.rightCode_cast (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (rightCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.rightWord (setAt L k i)) := by sorry
