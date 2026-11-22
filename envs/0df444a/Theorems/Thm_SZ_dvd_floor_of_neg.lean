-- Prove2me | Theorems.Thm_SZ_dvd_floor_of_neg
-- name    : SZ.dvd_floor_of_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:33.053109+00:00
-- url     : https://prove2.me/theorems/0663ef61-5571-4993-8588-efaf2abef39f
-- title:
--   SZ: dvd floor of neg
-- statement:
--   **Report §D.4 / plan Theorem C — designed total divisibility.**  If `m ∣ a` and
--   `m ∣ b - 1`, then every integral part `⌊ξ αⁿ⌋` of the closed-form `ξ = -β/(α-β)` is
--   divisible by `m`.  Compare [Dub06EO] Thm 6, which gives only `ε`-confinement of the
--   fractional parts, with an `ε`-dependent `ξ`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L163-L166
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L163-L166

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}

theorem SZ.dvd_floor_of_neg {m : ℤ} (h : Pair α β a b) (hβ : β < 0) (ha : m ∣ a)
    (hb : m ∣ (b - 1)) (n : ℕ) : m ∣ ⌊xiDesign α β * α ^ n⌋ := by sorry
