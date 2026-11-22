-- Prove2me | Theorems.Thm_SZ_floor_silver
-- name    : SZ.floor_silver
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:47:16.295967+00:00
-- url     : https://prove2.me/theorems/c1f6d4a0-2d52-4251-b5b3-1ea44aaa39cd
-- title:
--   SZ: floor silver
-- statement:
--   **The exact orbit.**  `⌊((2-√2)/4)·(1+√2)ⁿ⌋ = rec2 2 1 1 0 n - [2 ∣ n]` for every
--   `n ≥ 0`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L119-L123
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L119-L123

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.floor_silver (n : ℕ) :
    ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n⌋
      = rec2 2 1 1 0 n - (if n % 2 = 0 then 1 else 0) := by sorry
