-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_card
-- name    : ThreeSum.LocalMaskGraph.setAt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:17.268066+00:00
-- url     : https://prove2.me/theorems/d859dd13-be11-44a4-96d7-afa1785e5dcf
-- title:
--   Local Mask Graph: set At card
-- statement:
--   The Local Mask Graph construction uses the set At card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L33-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L33-L34

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

theorem ThreeSum.LocalMaskGraph.setAt_card {L h i : ℕ} (hi : i < vertexCount L h) : (setAt L h i).card = h := by sorry
