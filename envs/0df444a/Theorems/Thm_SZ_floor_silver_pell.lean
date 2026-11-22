-- Prove2me | Theorems.Thm_SZ_floor_silver_pell
-- name    : SZ.floor_silver_pell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:59.595184+00:00
-- url     : https://prove2.me/theorems/c1e50535-b631-4cc0-a2ff-fa70adcd927a
-- title:
--   SZ: floor silver pell
-- statement:
--   **The exact orbit, in Pell form.**  `⌊ξ (1+√2)^{n+1}⌋ = P_n - [2 ∤ n]`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L126-L135
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L126-L135

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.floor_silver_pell (n : ℕ) :
    ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ (n + 1)⌋
      = pell n - (if n % 2 = 0 then 0 else 1) := by sorry
