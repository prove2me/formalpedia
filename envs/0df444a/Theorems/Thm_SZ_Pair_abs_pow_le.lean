-- Prove2me | Theorems.Thm_SZ_Pair_abs_pow_le
-- name    : SZ.Pair.abs_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:46:12.849228+00:00
-- url     : https://prove2.me/theorems/05f39d9d-c62e-452b-865c-05bed889db8d
-- title:
--   Pair: abs pow le
-- statement:
--   `|βⁿ| ≤ 1` for every `n`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L89-L90
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L89-L90

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
open SZ.Pair
variable {α β : ℝ} {a b : ℤ}

theorem SZ.Pair.abs_pow_le (h : Pair α β a b) (n : ℕ) : |β ^ n| ≤ 1 := by sorry
