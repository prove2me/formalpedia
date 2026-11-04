-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_doubledAmbiguous_card
-- name    : ThreeSum.TernaryCoverProjection.doubledAmbiguous_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:14.672404+00:00
-- url     : https://prove2.me/theorems/c41df944-d0b3-4cc5-a108-9be59e39af0f
-- title:
--   Ternary Cover Projection: doubled Ambiguous card
-- statement:
--   The Ternary Cover Projection construction uses the doubled Ambiguous card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L142-L157
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L142-L157

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.doubledAmbiguous_card {L : ℕ} {α π : DigitType} (swap : Bool) (e : LocalEdge L α π)
    (hthirds : π 2 = 3 * α 2) :
    (doubledAmbiguous swap e).card = π 1 / 2 + π 2 / 3 := by sorry
