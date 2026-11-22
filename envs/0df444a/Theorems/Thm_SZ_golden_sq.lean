-- Prove2me | Theorems.Thm_SZ_golden_sq
-- name    : SZ.golden_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:51:22.244783+00:00
-- url     : https://prove2.me/theorems/9844d224-9cc6-43d2-a520-bf478732696f
-- title:
--   SZ: golden sq
-- statement:
--   The SZ construction uses the golden sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/GoldenS.lean#L58-L59
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/GoldenS.lean#L58-L59

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime
import Definitions.Def_SZ_GoldenS
set_option autoImplicit false
open SZ
open Real

theorem SZ.golden_sq : golden ^ 2 = golden + 1 := by sorry
