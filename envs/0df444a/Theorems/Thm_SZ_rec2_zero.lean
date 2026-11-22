-- Prove2me | Theorems.Thm_SZ_rec2_zero
-- name    : SZ.rec2_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:53.721429+00:00
-- url     : https://prove2.me/theorems/28b21818-06ab-425b-9f07-6e33c909eabb
-- title:
--   SZ: rec2 zero
-- statement:
--   The SZ construction uses the rec2 zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean#L54-L54
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean#L54-L54

import Definitions.Def_SZ_Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Trace
set_option autoImplicit false
open SZ

theorem SZ.rec2_zero (A B t₀ t₁ : ℤ) : rec2 A B t₀ t₁ 0 = t₀ := by sorry

attribute [defeq] SZ.rec2_zero
