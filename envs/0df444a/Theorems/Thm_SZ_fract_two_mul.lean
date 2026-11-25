-- Prove2me | Theorems.Thm_SZ_fract_two_mul
-- name    : SZ.fract_two_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:04:58.236486+00:00
-- url     : https://prove2.me/theorems/d84d4164-a0b0-4983-a073-3a3a511b98cc
-- title:
--   SZ: fract two mul
-- statement:
--   Where the fractional part is below `1/2`, doubling is **linear** on it.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L102-L109
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L102-L109

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
set_option autoImplicit false
open SZ

theorem SZ.fract_two_mul {u : ℝ} (h : Int.fract u < 1 / 2) :
    Int.fract (2 * u) = 2 * Int.fract u := by sorry
