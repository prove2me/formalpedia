-- Prove2me | Theorems.Thm_SZ_xiDesign_silver
-- name    : SZ.xiDesign_silver
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:47:15.837445+00:00
-- url     : https://prove2.me/theorems/53c0b53b-c3b9-4f31-9dac-3fbb6cfb7224
-- title:
--   SZ: xi Design silver
-- statement:
--   The designed multiplier at `1 + √2` is `ξ = (2 - √2)/4`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L106-L113
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L106-L113

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.xiDesign_silver :
    xiDesign (1 + Real.sqrt 2) (1 - Real.sqrt 2) = (2 - Real.sqrt 2) / 4 := by sorry
