-- Prove2me | Theorems.Thm_SZ_floor_oneAddSqrtThree
-- name    : SZ.floor_oneAddSqrtThree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:51:07.490021+00:00
-- url     : https://prove2.me/theorems/a646d933-311b-456f-9f22-00e23fc580b6
-- title:
--   SZ: floor one Add Sqrt Three
-- statement:
--   **The exact orbit at `ξ = 1/3`.**  `3 ⌊(1+√3)ⁿ/3⌋ = S_n - 2` for every `n ≥ 0`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadThm6.lean#L101-L119
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadThm6.lean#L101-L119

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_QuadThm6
set_option autoImplicit false
open SZ
open Real

theorem SZ.floor_oneAddSqrtThree (n : ℕ) :
    3 * ⌊(1 / 3 : ℝ) * (1 + Real.sqrt 3) ^ n⌋ = rec2 2 2 2 2 n - 2 := by sorry
