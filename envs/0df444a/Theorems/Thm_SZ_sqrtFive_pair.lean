-- Prove2me | Theorems.Thm_SZ_sqrtFive_pair
-- name    : SZ.sqrtFive_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:33.789985+00:00
-- url     : https://prove2.me/theorems/138bb817-d533-45dd-8e2f-4495d313c053
-- title:
--   SZ: sqrt Five pair
-- statement:
--   `2 + √5` and `2 - √5` are the roots of `x² = 4x + 1`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L100-L105
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L100-L105

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}

theorem SZ.sqrtFive_pair : Pair (2 + Real.sqrt 5) (2 - Real.sqrt 5) 4 1 := by sorry
