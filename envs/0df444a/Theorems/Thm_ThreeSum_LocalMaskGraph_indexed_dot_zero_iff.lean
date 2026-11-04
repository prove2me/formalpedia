-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_indexed_dot_zero_iff
-- name    : ThreeSum.LocalMaskGraph.indexed_dot_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:49.814315+00:00
-- url     : https://prove2.me/theorems/bea48c7f-5a75-420e-ba52-e1e23d70b63a
-- title:
--   Local Mask Graph: indexed dot zero iff
-- statement:
--   The Local Mask Graph construction uses the indexed dot zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L79-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L79-L84

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators

theorem ThreeSum.LocalMaskGraph.indexed_dot_zero_iff {L h i j : ℕ}
    (hi : i < vertexCount L h) (hj : j < vertexCount L h) :
    LightBooleanDot.dot (LightMaskBits.bit L (maskAt L h i))
      (LightMaskBits.bit L (maskAt L h j)) L = 0 ↔ Disjoint (setAt L h i) (setAt L h j) := by sorry
