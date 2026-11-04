-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverGenericProjection_mixedFiber_generic_card_le_one
-- name    : ThreeSum.TernaryCoverGenericProjection.mixedFiber_generic_card_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:30.579494+00:00
-- url     : https://prove2.me/theorems/f43b29bb-9131-472f-80f8-ba17a27ed509
-- title:
--   Ternary Cover Generic Projection: mixed Fiber generic card le one
-- statement:
--   Generic full-word projection fibers contain at most one genuine edge.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGenericProjection.lean#L45-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGenericProjection.lean#L45-L58

import Definitions.Def_Submission_ThreeSum_TernaryProjectionCells
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverGenericProjection
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open ThreeSum ThreeSum.TernaryCoverGenericProjection
open Finset TernaryJointType TernaryCoverLocal
variable {K : Type*} [Field K]
variable {L p : ℕ}

theorem ThreeSum.TernaryCoverGenericProjection.mixedFiber_generic_card_le_one [Fact p.Prime] (α π : DigitType)
    {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (hsum : a+b ≠ 0) (heq : a ≠ b) (hhalf : 2*a ≠ b) (hdouble : a ≠ 2*b)
    (q : Fin L → ZMod p) : (mixedFiber α π a b q).card ≤ 1 := by sorry
