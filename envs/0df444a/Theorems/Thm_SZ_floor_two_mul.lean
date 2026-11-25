-- Prove2me | Theorems.Thm_SZ_floor_two_mul
-- name    : SZ.floor_two_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:03:23.488823+00:00
-- url     : https://prove2.me/theorems/2b320d13-eae4-415c-b970-000ad58faf71
-- title:
--   SZ: floor two mul
-- statement:
--   `⌊2u⌋ = 2⌊u⌋ + ⌊2{u}⌋`: the integral part of a doubled real, split off its
--   fractional part.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L67-L71
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L67-L71

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
set_option autoImplicit false
open SZ

theorem SZ.floor_two_mul (u : ℝ) : ⌊2 * u⌋ = 2 * ⌊u⌋ + ⌊2 * Int.fract u⌋ := by sorry
