-- Prove2me | Theorems.Thm_SZ_silver_conj_neg
-- name    : SZ.silver_conj_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:44:01.250171+00:00
-- url     : https://prove2.me/theorems/78ecb652-fe59-4121-9daf-f9f193daae57
-- title:
--   SZ: silver conj neg
-- statement:
--   The SZ construction uses the silver conj neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L103-L103
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L103-L103

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.silver_conj_neg : (1 : ℝ) - Real.sqrt 2 < 0 := by sorry
