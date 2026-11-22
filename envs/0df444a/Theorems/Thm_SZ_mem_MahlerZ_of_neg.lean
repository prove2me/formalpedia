-- Prove2me | Theorems.Thm_SZ_mem_MahlerZ_of_neg
-- name    : SZ.mem_MahlerZ_of_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:30.131551+00:00
-- url     : https://prove2.me/theorems/fc821241-18b3-4e5e-a6f8-cded116f7e6c
-- title:
--   SZ: mem Mahler Z of neg
-- statement:
--   **The design.**  A real quadratic pair with a negative second conjugate, even `a` and
--   odd `b` puts `α` in `𝒵`, with the explicit witness `ξ = -β/(α-β)`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L170-L178
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L170-L178

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}

theorem SZ.mem_MahlerZ_of_neg (h : Pair α β a b) (hβ : β < 0) (ha : Even a) (hb : ¬ Even b) :
    α ∈ MahlerZ := by sorry
