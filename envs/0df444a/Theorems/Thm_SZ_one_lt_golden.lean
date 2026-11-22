-- Prove2me | Theorems.Thm_SZ_one_lt_golden
-- name    : SZ.one_lt_golden
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:47:52.926511+00:00
-- url     : https://prove2.me/theorems/eea5208d-3f8f-4088-8401-24e784b7d0a6
-- title:
--   SZ: one lt golden
-- statement:
--   The SZ construction uses the one lt golden property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/GoldenS.lean#L55-L56
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/GoldenS.lean#L55-L56

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime
import Definitions.Def_SZ_GoldenS
set_option autoImplicit false
open SZ
open Real

theorem SZ.one_lt_golden : 1 < golden := by sorry
