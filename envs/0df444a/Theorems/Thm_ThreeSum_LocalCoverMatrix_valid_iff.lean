-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverMatrix_valid_iff
-- name    : ThreeSum.LocalCoverMatrix.valid_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:39.476062+00:00
-- url     : https://prove2.me/theorems/9ecc8289-7944-4a9b-a366-9660089a6378
-- title:
--   Local Cover Matrix: valid iff
-- statement:
--   The Local Cover Matrix construction uses the valid iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean#L66-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean#L66-L78

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}

theorem ThreeSum.LocalCoverMatrix.valid_iff (w : Weight L (LocalField h)) {B i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k) :
    valid w k B i=1 ↔
      Disjoint (setAt L k (i/LocalMaskGraph.vertexCount L k))
        (setAt L k (i%LocalMaskGraph.vertexCount L k)) ∧
      leftCount w k (leftCode w k (i/LocalMaskGraph.vertexCount L k)) ≤ B ∧
      rightCount w k (rightCode w k (i%LocalMaskGraph.vertexCount L k)) ≤ B := by sorry
