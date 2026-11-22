-- Prove2me | Theorems.Thm_P2M_SZ_xiDesign__lt_one_4e35a34576eb
-- name    : P2M_SZ_xiDesign__lt_one_4e35a34576eb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:46:38.42905+00:00
-- url     : https://prove2.me/theorems/fbf8caf6-ae30-4caf-a90b-7e2e27c805cf
-- title:
--   P2 M SZ xi Design  lt one 4e35a34576eb: P2 M SZ xi Design  lt one 4e35a34576eb
-- statement:
--   The P2 M SZ xi Design  lt one 4e35a34576eb construction uses the P2 M SZ xi Design  lt one 4e35a34576eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L110-L113
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L110-L113

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}

theorem P2M_SZ_xiDesign__lt_one_4e35a34576eb (h : Pair α β a b) (hβ : β < 0) : xiDesign' α β < 1 := by sorry

alias «SZ».«xiDesign'_lt_one» := P2M_SZ_xiDesign__lt_one_4e35a34576eb
