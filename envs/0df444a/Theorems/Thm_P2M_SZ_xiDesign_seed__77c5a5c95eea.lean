-- Prove2me | Theorems.Thm_P2M_SZ_xiDesign_seed__77c5a5c95eea
-- name    : P2M_SZ_xiDesign_seed__77c5a5c95eea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:46:35.695804+00:00
-- url     : https://prove2.me/theorems/134de124-6251-49ce-b421-e1cf5aafd8e3
-- title:
--   P2 M SZ xi Design seed  77c5a5c95eea: P2 M SZ xi Design seed  77c5a5c95eea
-- statement:
--   The two seeds of the design are the integers `1` and `0`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L116-L121
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L116-L121

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}

theorem P2M_SZ_xiDesign_seed__77c5a5c95eea (h : Pair α β a b) :
    xiDesign α β + xiDesign' α β = ((1 : ℤ) : ℝ) := by sorry

alias «SZ».«xiDesign_seed₀» := P2M_SZ_xiDesign_seed__77c5a5c95eea
