-- Prove2me | Theorems.Thm_SZ_Pair_sub_pos
-- name    : SZ.Pair.sub_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:54.191091+00:00
-- url     : https://prove2.me/theorems/1ec16f9b-be36-420f-a053-72686f76f3c2
-- title:
--   Pair: sub pos
-- statement:
--   The Pair construction uses the sub pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L85-L86
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L85-L86

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
open SZ.Pair
variable {α β : ℝ} {a b : ℤ}

theorem SZ.Pair.sub_pos (h : Pair α β a b) : 0 < α - β := by sorry
