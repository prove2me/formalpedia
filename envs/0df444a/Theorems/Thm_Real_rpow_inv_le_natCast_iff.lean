-- Prove2me | Theorems.Thm_Real_rpow_inv_le_natCast_iff
-- name    : Real.rpow_inv_le_natCast_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:56.257995+00:00
-- url     : https://prove2.me/theorems/5f46c7fe-287f-4d62-a462-c9b8f7f88a94
-- title:
--   Real: rpow inv le nat Cast iff
-- statement:
--   The `e`-th root of `t` is at most `x` exactly if `t ≤ x ^ e`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L93-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L93-L97

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Real

theorem Real.rpow_inv_le_natCast_iff {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (t : ℝ) ^ ((e : ℝ)⁻¹) ≤ (x : ℝ) ↔ t ≤ x ^ e := by sorry
