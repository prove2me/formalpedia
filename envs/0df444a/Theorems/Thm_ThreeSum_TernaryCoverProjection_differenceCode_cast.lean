-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_differenceCode_cast
-- name    : ThreeSum.TernaryCoverProjection.differenceCode_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:31.246354+00:00
-- url     : https://prove2.me/theorems/2876556a-a1af-437a-b2aa-8da40520bd7f
-- title:
--   Ternary Cover Projection: difference Code cast
-- statement:
--   The Ternary Cover Projection construction uses the difference Code cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L24-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L24-L30

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.differenceCode_cast (p : ℕ) (a b : Fin 3) :
    (differenceCode a b : ZMod p) = (a.val : ZMod p) - (b.val : ZMod p) + 2 := by sorry
