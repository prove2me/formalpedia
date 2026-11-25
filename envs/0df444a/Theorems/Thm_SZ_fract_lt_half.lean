-- Prove2me | Theorems.Thm_SZ_fract_lt_half
-- name    : SZ.fract_lt_half
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:04:58.216523+00:00
-- url     : https://prove2.me/theorems/7f8619a1-7073-4130-aa3f-48fa0e24f53a
-- title:
--   SZ: fract lt half
-- statement:
--   **The parity step.**  If both `⌊u⌋` and `⌊2u⌋` are even, then `{u} < 1/2`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L86-L99
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L86-L99

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
set_option autoImplicit false
open SZ

theorem SZ.fract_lt_half {u : ℝ} (h : Even ⌊u⌋) (h2 : Even ⌊2 * u⌋) : Int.fract u < 1 / 2 := by sorry
