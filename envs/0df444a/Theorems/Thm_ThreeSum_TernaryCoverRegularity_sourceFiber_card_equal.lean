-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_sourceFiber_card_equal
-- name    : ThreeSum.TernaryCoverRegularity.sourceFiber_card_equal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:04.018852+00:00
-- url     : https://prove2.me/theorems/84f85af4-0f22-459a-b513-ee08a143f52a
-- title:
--   Ternary Cover Regularity: source Fiber card equal
-- statement:
--   Actual degrees are equal; this is an equivalence of original local edges.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L78-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L78-L89

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.sourceFiber_card_equal {α π : DigitType} {a b : TritWord L}
    (ha : HasType a α) (hb : HasType b α) :
    Fintype.card (sourceFiber α π a) = Fintype.card (sourceFiber α π b) := by sorry
