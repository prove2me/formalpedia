-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_marked_card
-- name    : ThreeSum.TernaryCoverProjection.marked_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:09.548193+00:00
-- url     : https://prove2.me/theorems/f0f938ee-cdab-4880-b58e-51070b8e9d6e
-- title:
--   Ternary Cover Projection: marked card
-- statement:
--   The Ternary Cover Projection construction uses the marked card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L56-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L56-L64

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.marked_card {L : ℕ} {α π : DigitType} (e : LocalEdge L α π)
    (hthirds : π 2 = 3 * α 2) :
    (marked e).card = π 2 / 3 := by sorry
