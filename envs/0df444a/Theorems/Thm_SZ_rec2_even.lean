-- Prove2me | Theorems.Thm_SZ_rec2_even
-- name    : SZ.rec2_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:48:03.148783+00:00
-- url     : https://prove2.me/theorems/7c8ad9b4-f2eb-4251-b131-4484c26031dd
-- title:
--   SZ: rec2 even
-- statement:
--   **The constant pattern.**  Even seeds give an even sequence, whatever `A` and `B`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean#L88-L95
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean#L88-L95

import Definitions.Def_SZ_Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Trace
set_option autoImplicit false
open SZ

theorem SZ.rec2_even {A B t₀ t₁ : ℤ} (h0 : Even t₀) (h1 : Even t₁) (n : ℕ) :
    Even (rec2 A B t₀ t₁ n) := by sorry
