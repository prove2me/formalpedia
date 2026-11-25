-- Prove2me | Theorems.Thm_SZ_one_lt_sqrt_two
-- name    : SZ.one_lt_sqrt_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:05:55.060074+00:00
-- url     : https://prove2.me/theorems/27b98e33-a761-4165-90aa-ccd64b133191
-- title:
--   SZ: one lt sqrt two
-- statement:
--   The SZ construction uses the one lt sqrt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L155-L157
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L155-L157

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
set_option autoImplicit false
open SZ

theorem SZ.one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by sorry
