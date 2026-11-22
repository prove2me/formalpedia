-- Prove2me | Theorems.Thm_P2M_SZ_xiDesign__pos_7fd4c80a1ef7
-- name    : P2M_SZ_xiDesign__pos_7fd4c80a1ef7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:46:15.016942+00:00
-- url     : https://prove2.me/theorems/6669ce89-5adc-430f-8fe9-61ab250a027c
-- title:
--   P2 M SZ xi Design  pos 7fd4c80a1ef7: P2 M SZ xi Design  pos 7fd4c80a1ef7
-- statement:
--   The P2 M SZ xi Design  pos 7fd4c80a1ef7 construction uses the P2 M SZ xi Design  pos 7fd4c80a1ef7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L107-L108
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L107-L108

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}

theorem P2M_SZ_xiDesign__pos_7fd4c80a1ef7 (h : Pair α β a b) : 0 < xiDesign' α β := by sorry

alias «SZ».«xiDesign'_pos» := P2M_SZ_xiDesign__pos_7fd4c80a1ef7
