-- Prove2me | Theorems.Thm_SZ_Pair_sq_alpha
-- name    : SZ.Pair.sq_alpha
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:58.979835+00:00
-- url     : https://prove2.me/theorems/4d5c94d5-80af-4892-a0f4-86efd36c555c
-- title:
--   Pair: sq alpha
-- statement:
--   The Pair construction uses the sq alpha property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L73-L77
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L73-L77

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
open SZ.Pair
variable {α β : ℝ} {a b : ℤ}

theorem SZ.Pair.sq_alpha (h : Pair α β a b) : α ^ 2 = (a : ℝ) * α + (b : ℝ) := by sorry
