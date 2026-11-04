-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_dot_zero_iff
-- name    : ThreeSum.LocalMaskGraph.dot_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:07.244958+00:00
-- url     : https://prove2.me/theorems/432fb0e8-f343-4a1f-95ef-4cc1de10a5c5
-- title:
--   Local Mask Graph: dot zero iff
-- statement:
--   The Local Mask Graph construction uses the dot zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L73-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L73-L77

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

theorem ThreeSum.LocalMaskGraph.dot_zero_iff {L : ℕ} (s t : Finset (Fin L)) :
    LightBooleanDot.dot (LightMaskBits.bit L (subsetMask s))
      (LightMaskBits.bit L (subsetMask t)) L = 0 ↔ Disjoint s t := by sorry
