-- Prove2me | Theorems.Thm_P2M_SZ_xiDesign_seed__46b539b85d21
-- name    : P2M_SZ_xiDesign_seed__46b539b85d21
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:46:39.69196+00:00
-- url     : https://prove2.me/theorems/24d77716-f075-4591-a11b-2ad168fbcee3
-- title:
--   P2 M SZ xi Design seed  46b539b85d21: P2 M SZ xi Design seed  46b539b85d21
-- statement:
--   The P2 M SZ xi Design seed  46b539b85d21 construction uses the P2 M SZ xi Design seed  46b539b85d21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L123-L128
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean#L123-L128

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}

theorem P2M_SZ_xiDesign_seed__46b539b85d21 (h : Pair α β a b) :
    xiDesign α β * α + xiDesign' α β * β = ((0 : ℤ) : ℝ) := by sorry

alias «SZ».«xiDesign_seed₁» := P2M_SZ_xiDesign_seed__46b539b85d21
