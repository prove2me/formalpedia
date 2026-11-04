-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_differenceFiber_card_le
-- name    : ThreeSum.TernaryCoverProjection.differenceFiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:10.468197+00:00
-- url     : https://prove2.me/theorems/fd87fc37-1a0b-445b-a604-9097165402d6
-- title:
--   Ternary Cover Projection: difference Fiber card le
-- statement:
--   The Ternary Cover Projection construction uses the difference Fiber card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L70-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L70-L108

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.differenceFiber_card_le {L p : ℕ} (α π : DigitType)
    (hthirds : π 2 = 3 * α 2) (hp : 4 < p) (q : Fin L → ZMod p) :
    (differenceFiber α π q).card ≤ L.choose (π 2 / 3) := by sorry
