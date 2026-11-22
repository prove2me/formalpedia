-- Prove2me | Theorems.Thm_SZ_pell_one
-- name    : SZ.pell_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:02.775824+00:00
-- url     : https://prove2.me/theorems/5ffa85e7-ced2-46f4-bf73-c9ae4f15d43d
-- title:
--   SZ: pell one
-- statement:
--   The SZ construction uses the pell one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L70-L70
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L70-L70

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.pell_one : pell 1 = 1 := by sorry

attribute [defeq] SZ.pell_one
