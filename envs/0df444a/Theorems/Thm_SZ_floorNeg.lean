-- Prove2me | Theorems.Thm_SZ_floorNeg
-- name    : SZ.floorNeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:44:47.45427+00:00
-- url     : https://prove2.me/theorems/a21b753d-8bab-45df-9abe-9f4ecfa6f7d5
-- title:
--   SZ: floor Neg
-- statement:
--   **The exact floor identity.**  For a negative second conjugate the designed `ξ`
--   produces `⌊ξ αⁿ⌋ = rec2 a b 1 0 n - 1` at even `n` and `= rec2 a b 1 0 n` at odd `n`,
--   for *every* `n ≥ 0` — no threshold, no tail closure.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L133-L157
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L133-L157

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}

theorem SZ.floorNeg (h : Pair α β a b) (hβ : β < 0) (n : ℕ) :
    ⌊xiDesign α β * α ^ n⌋ = rec2 a b 1 0 n - (if n % 2 = 0 then 1 else 0) := by sorry
