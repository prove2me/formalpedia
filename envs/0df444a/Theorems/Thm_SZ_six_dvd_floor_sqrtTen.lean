-- Prove2me | Theorems.Thm_SZ_six_dvd_floor_sqrtTen
-- name    : SZ.six_dvd_floor_sqrtTen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:30.69684+00:00
-- url     : https://prove2.me/theorems/8d81fb75-4a1b-4987-a87e-1bf95649431a
-- title:
--   SZ: six dvd floor sqrt Ten
-- statement:
--   **Report §D.4 in one instance.**  `6 ∣ ⌊ξ (3+√10)ⁿ⌋` for every `n ≥ 0`, with the
--   closed-form `ξ = -(3-√10)/(2√10)`.  Here `a = 6 ≡ 0` and `b = 1 ≡ 1` modulo `6`
--   simultaneously, so the same `ξ` also realises the moduli `2` and `3`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L127-L129
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L127-L129

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}

theorem SZ.six_dvd_floor_sqrtTen (n : ℕ) :
    (6 : ℤ) ∣ ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ := by sorry
