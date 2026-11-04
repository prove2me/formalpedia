-- Prove2me | Theorems.Thm_ThreeSum_TernaryLocalParameters_fixed_mixedFiber_cap
-- name    : ThreeSum.TernaryLocalParameters.fixed_mixedFiber_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:39.306261+00:00
-- url     : https://prove2.me/theorems/3e6017b1-9058-4e17-b84e-19b4d8c0868f
-- title:
--   Ternary Local Parameters: fixed mixed Fiber cap
-- statement:
--   All full scalar projection fibers are paid by the sole local prime guard.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L69-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L69-L78

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.TernaryLocalParameters.fixed_mixedFiber_cap (m p : ℕ) [Fact p.Prime] (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    {a b : ZMod p} (hab : a ≠ 0 ∨ b ≠ 0) (q : Fin (fixedLength m) → ZMod p) :
    (TernaryCoverGenericProjection.mixedFiber (fixedAlpha m) (fixedPi m) a b q).card ≤ p := by sorry
