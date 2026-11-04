-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_doubledFiber_card_le
-- name    : ThreeSum.TernaryCoverProjection.doubledFiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:19.792194+00:00
-- url     : https://prove2.me/theorems/8d04af78-3c8e-43f3-9fd9-3c2ca3934fd4
-- title:
--   Ternary Cover Projection: doubled Fiber card le
-- statement:
--   The Ternary Cover Projection construction uses the doubled Fiber card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L163-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L163-L201

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.doubledFiber_card_le {L p : ℕ} (swap : Bool) (α π : DigitType)
    (hthirds : π 2 = 3 * α 2) (hp : 4 < p) (q : Fin L → ZMod p) :
    (doubledFiber swap α π q).card ≤ 2 ^ (π 1 / 2 + π 2 / 3) := by sorry
