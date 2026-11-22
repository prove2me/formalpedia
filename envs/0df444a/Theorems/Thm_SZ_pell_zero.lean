-- Prove2me | Theorems.Thm_SZ_pell_zero
-- name    : SZ.pell_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:53.766319+00:00
-- url     : https://prove2.me/theorems/37fae058-8638-4c55-86c3-88ab992ba567
-- title:
--   SZ: pell zero
-- statement:
--   The SZ construction uses the pell zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L67-L67
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L67-L67

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.pell_zero : pell 0 = 0 := by sorry

attribute [defeq] SZ.pell_zero
