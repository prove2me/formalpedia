-- Prove2me | Theorems.Thm_SZ_sqrtThree_pair
-- name    : SZ.sqrtThree_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:45:42.884267+00:00
-- url     : https://prove2.me/theorems/4ff85e0a-8427-4641-a5ba-043f2584bd27
-- title:
--   SZ: sqrt Three pair
-- statement:
--   `1 + √3` and `1 - √3` are the two roots of `x² = 2x + 2`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadThm6.lean#L63-L69
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadThm6.lean#L63-L69

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_QuadThm6
set_option autoImplicit false
open SZ
open Real

theorem SZ.sqrtThree_pair : Pair (1 + Real.sqrt 3) (1 - Real.sqrt 3) 2 2 := by sorry
