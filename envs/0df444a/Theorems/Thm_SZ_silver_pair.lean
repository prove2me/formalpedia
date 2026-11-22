-- Prove2me | Theorems.Thm_SZ_silver_pair
-- name    : SZ.silver_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:50.531154+00:00
-- url     : https://prove2.me/theorems/437abfed-0946-4d1a-a682-62f5fe785a29
-- title:
--   SZ: silver pair
-- statement:
--   `1 + √2` and `1 - √2` are the two roots of `x² = 2x + 1`, and the second lies in the
--   open unit disc.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L96-L101
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L96-L101

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.silver_pair : Pair (1 + Real.sqrt 2) (1 - Real.sqrt 2) 2 1 := by sorry
