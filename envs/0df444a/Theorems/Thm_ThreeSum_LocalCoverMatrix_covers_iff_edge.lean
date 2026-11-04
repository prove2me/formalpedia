-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverMatrix_covers_iff_edge
-- name    : ThreeSum.LocalCoverMatrix.covers_iff_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:54.691811+00:00
-- url     : https://prove2.me/theorems/514725a0-768c-4fcd-81c9-78a6f32e0bf4
-- title:
--   Local Cover Matrix: covers iff edge
-- statement:
--   The Local Cover Matrix construction uses the covers iff edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean#L49-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean#L49-L64

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}

theorem ThreeSum.LocalCoverMatrix.covers_iff_edge (w : Weight L (LocalField h)) (k B : ℕ)
    (a b : LocalField h) :
    Covers L k B w (a,b) ↔ ∃ e : LocalGraph.Edge L k,
      HashFamily.hashValue w (LocalGraph.left e)=a ∧
      HashFamily.hashValue w (LocalGraph.right e)=b ∧
      HashFamily.bucketSize (LocalGraph.leftVertices L k) w a ≤ B ∧
      HashFamily.bucketSize (LocalGraph.rightVertices L k) w b ≤ B := by sorry
