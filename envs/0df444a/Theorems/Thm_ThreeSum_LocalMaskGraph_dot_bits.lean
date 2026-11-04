-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_dot_bits
-- name    : ThreeSum.LocalMaskGraph.dot_bits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:09.672939+00:00
-- url     : https://prove2.me/theorems/4d5537c5-5dc2-40d1-9ac7-4c2388f9d7d1
-- title:
--   Local Mask Graph: dot bits
-- statement:
--   The Local Mask Graph construction uses the dot bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L59-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L59-L71

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

theorem ThreeSum.LocalMaskGraph.dot_bits {L : ℕ} (s t : Finset (Fin L)) :
    LightBooleanDot.dot (LightMaskBits.bit L (subsetMask s))
      (LightMaskBits.bit L (subsetMask t)) L = (s ∩ t).card := by sorry
