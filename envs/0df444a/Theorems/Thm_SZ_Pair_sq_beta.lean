-- Prove2me | Theorems.Thm_SZ_Pair_sq_beta
-- name    : SZ.Pair.sq_beta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:20.158793+00:00
-- url     : https://prove2.me/theorems/85b3ffab-f770-4ecc-9819-bc4fe50ef868
-- title:
--   Pair: sq beta
-- statement:
--   The Pair construction uses the sq beta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L79-L83
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L79-L83

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
open SZ.Pair
variable {α β : ℝ} {a b : ℤ}

theorem SZ.Pair.sq_beta (h : Pair α β a b) : β ^ 2 = (a : ℝ) * β + (b : ℝ) := by sorry
