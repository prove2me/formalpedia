-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverOutputCap_outputFiber_card_le_product
-- name    : ThreeSum.TernaryCoverOutputCap.outputFiber_card_le_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:13.872229+00:00
-- url     : https://prove2.me/theorems/edfba39f-55b1-4be8-b245-c7c26b930eef
-- title:
--   Ternary Cover Output Cap: output Fiber card le product
-- statement:
--   Fixed-output choices are bounded before any endpoint-type restrictions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L39-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L39-L43

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverOutputCap.outputFiber_card_le_product (α π : DigitType) (q : TritWord L) :
    Fintype.card (outputFiber α π q) ≤ ∏ i, ((q i).val+1) := by sorry
