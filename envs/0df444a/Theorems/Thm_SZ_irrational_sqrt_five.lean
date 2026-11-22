-- Prove2me | Theorems.Thm_SZ_irrational_sqrt_five
-- name    : SZ.irrational_sqrt_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:51:27.345053+00:00
-- url     : https://prove2.me/theorems/952b26da-bdee-4b3d-ad83-7375f4ab68d0
-- title:
--   SZ: irrational sqrt five
-- statement:
--   The SZ construction uses the irrational sqrt five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/GoldenS.lean#L61-L63
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/GoldenS.lean#L61-L63

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime
import Definitions.Def_SZ_GoldenS
set_option autoImplicit false
open SZ
open Real

theorem SZ.irrational_sqrt_five : Irrational (Real.sqrt 5) := by sorry
