-- Prove2me | Theorems.Thm_SZ_even_floor_silver
-- name    : SZ.even_floor_silver
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:12.614841+00:00
-- url     : https://prove2.me/theorems/8174ae77-6e75-45da-a99a-db88c8ddaf0b
-- title:
--   SZ: even floor silver
-- statement:
--   Every integral part is even, spelled out at the explicit witness.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L145-L151
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L145-L151

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.even_floor_silver (n : ℕ) :
    Even ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n⌋ := by sorry
