-- Prove2me | Theorems.Thm_SZ_floor_two_fract_cases
-- name    : SZ.floor_two_fract_cases
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:03:24.799315+00:00
-- url     : https://prove2.me/theorems/d97c1616-0c3b-4139-b56a-7c5ab6a91058
-- title:
--   SZ: floor two fract cases
-- statement:
--   `⌊2{u}⌋` is `0` or `1`, since `0 ≤ 2{u} < 2`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L74-L83
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L74-L83

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
set_option autoImplicit false
open SZ

theorem SZ.floor_two_fract_cases (u : ℝ) : ⌊2 * Int.fract u⌋ = 0 ∨ ⌊2 * Int.fract u⌋ = 1 := by sorry
