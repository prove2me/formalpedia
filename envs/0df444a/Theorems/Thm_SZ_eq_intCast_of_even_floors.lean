-- Prove2me | Theorems.Thm_SZ_eq_intCast_of_even_floors
-- name    : SZ.eq_intCast_of_even_floors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:00.676703+00:00
-- url     : https://prove2.me/theorems/56492746-4015-4ad7-94a4-3f9c2180342a
-- title:
--   SZ: eq int Cast of even floors
-- statement:
--   **Rigidity.**  If `⌊t 2ᵏ⌋` is even for every `k ≥ 0`, then `t` is an even integer.
--   This is the whole obstruction at base `2`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L146-L151
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L146-L151

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
set_option autoImplicit false
open SZ

theorem SZ.eq_intCast_of_even_floors {t : ℝ} (h : ∀ k : ℕ, Even ⌊t * 2 ^ k⌋) :
    ∃ z : ℤ, Even z ∧ t = (z : ℝ) := by sorry
