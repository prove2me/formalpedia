-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverOutputCap_outputFiber_card_le
-- name    : ThreeSum.TernaryCoverOutputCap.outputFiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:58.700877+00:00
-- url     : https://prove2.me/theorems/7a9ebeda-e4f6-466c-9b69-1f99d6b8372f
-- title:
--   Ternary Cover Output Cap: output Fiber card le
-- statement:
--   The output partition cap is 2^π₁3^π₂ for every genuine output type.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L62-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L62-L66

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverOutputCap.outputFiber_card_le (α π : DigitType) (q : TritWord L) (hq : HasType q π) :
    Fintype.card (outputFiber α π q) ≤ 2^(π 1) * 3^(π 2) := by sorry
