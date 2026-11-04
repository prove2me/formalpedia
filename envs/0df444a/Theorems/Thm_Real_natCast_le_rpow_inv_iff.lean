-- Prove2me | Theorems.Thm_Real_natCast_le_rpow_inv_iff
-- name    : Real.natCast_le_rpow_inv_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:56.401368+00:00
-- url     : https://prove2.me/theorems/0b4bd796-71c8-4583-abe3-973c4ff5e68d
-- title:
--   Real: nat Cast le rpow inv iff
-- statement:
--   `x` is at most the `e`-th root of `t` exactly if `x ^ e ≤ t`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L86-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L86-L90

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Real

theorem Real.natCast_le_rpow_inv_iff {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (x : ℝ) ≤ (t : ℝ) ^ ((e : ℝ)⁻¹) ↔ x ^ e ≤ t := by sorry
