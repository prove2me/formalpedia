-- Prove2me | Theorems.Thm_SZ_fract_silver
-- name    : SZ.fract_silver
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:15.593343+00:00
-- url     : https://prove2.me/theorems/7efec544-69ea-41b4-aa39-55f450bcb1ba
-- title:
--   SZ: fract silver
-- statement:
--   **Report §E.3's corner.**  The fractional parts of the witness orbit sit within
--   `ξ̄ |ᾱ|ⁿ` of `1` at even `n` and of `0` at odd `n`; since `|ᾱ| = √2 - 1 < 1`, the limit
--   set is the two-point set `{0,1}` — while every integral part stays even.  ([DubA06] Thm 2
--   bounds the limit set of `{ξ αⁿ}` for a Pisot `α` and `ξ = f(α)` with `deg f < deg α`; two
--   points is the least this witness can achieve, not a general lower bound, since Thm 2(i)
--   allows a single limit point in `(0,1)`.)
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L161-L193
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L161-L193

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.fract_silver (n : ℕ) :
    |Int.fract ((2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n)
      - (if n % 2 = 0 then 1 else 0)|
      ≤ |(1 : ℝ) - Real.sqrt 2| ^ n := by sorry
