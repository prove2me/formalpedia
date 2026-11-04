-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixed_mixedFiber_cap
-- name    : ThreeSum.WeightedGlobalLocalParameters.fixed_mixedFiber_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:38.924425+00:00
-- url     : https://prove2.me/theorems/3b175a46-8d83-4b5f-b018-72145622ab85
-- title:
--   Weighted Global Local Parameters: fixed mixed Fiber cap
-- statement:
--   All full scalar projection fibers are paid by the sole local prime guard.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L75-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L75-L84

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.WeightedGlobalLocalParameters.fixed_mixedFiber_cap (m p : ℕ) [Fact p.Prime] (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    {a b : ZMod p} (hab : a ≠ 0 ∨ b ≠ 0) (q : Fin (fixedLength m) → ZMod p) :
    (TernaryCoverGenericProjection.mixedFiber (fixedAlpha m) (fixedPi m) a b q).card ≤ p := by sorry
