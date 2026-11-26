-- Prove2me | Theorems.Thm_Sqrt6KissingBound_planePoint_inner
-- name    : Sqrt6KissingBound.planePoint_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:17:54.943803+00:00
-- url     : https://prove2.me/theorems/dcd169fd-b12a-4261-bf5a-71f5658186de
-- title:
--   Sqrt6 Kissing Bound: plane Point inner
-- statement:
--   The Sqrt6 Kissing Bound construction uses the plane Point inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L33-L35
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L33-L35

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.planePoint_inner (x y u v : ℝ) :
    inner ℝ (planePoint x y) (planePoint u v) = x * u + y * v := by sorry
