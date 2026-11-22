-- Prove2me | Theorems.Thm_SZ_sqrtTen_pair
-- name    : SZ.sqrtTen_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:44:00.949153+00:00
-- url     : https://prove2.me/theorems/927b2e42-d9e5-483a-9619-fa7894e8173e
-- title:
--   SZ: sqrt Ten pair
-- statement:
--   `3 + √10` and `3 - √10` are the roots of `x² = 6x + 1`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L114-L119
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L114-L119

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}

theorem SZ.sqrtTen_pair : Pair (3 + Real.sqrt 10) (3 - Real.sqrt 10) 6 1 := by sorry
