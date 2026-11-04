-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_doubledCode_lt
-- name    : ThreeSum.TernaryCoverProjection.doubledCode_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:21.093476+00:00
-- url     : https://prove2.me/theorems/2d01f4f3-d73b-4abc-b8de-45149ce1440f
-- title:
--   Ternary Cover Projection: doubled Code lt
-- statement:
--   The Ternary Cover Projection construction uses the doubled Code lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L116-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L116-L118

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.doubledCode_lt (swap : Bool) (a b : Fin 3) (hab : a.val + b.val ≤ 2) :
    doubledCode swap a b < 5 := by sorry
