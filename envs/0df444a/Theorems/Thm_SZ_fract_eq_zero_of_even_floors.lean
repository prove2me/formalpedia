-- Prove2me | Theorems.Thm_SZ_fract_eq_zero_of_even_floors
-- name    : SZ.fract_eq_zero_of_even_floors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:05:27.770592+00:00
-- url     : https://prove2.me/theorems/7dccacef-765f-47ba-a2ab-c5bc8398798c
-- title:
--   SZ: fract eq zero of even floors
-- statement:
--   **Rigidity, the fractional half.**  If `⌊t 2ᵏ⌋` is even for every `k ≥ 0` then
--   `{t} = 0`: the orbit satisfies `{t 2ᵏ} = 2ᵏ {t} < 1/2`, and `2ᵏ` is unbounded.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L115-L142
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L115-L142

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
set_option autoImplicit false
open SZ

theorem SZ.fract_eq_zero_of_even_floors {t : ℝ} (h : ∀ k : ℕ, Even ⌊t * 2 ^ k⌋) :
    Int.fract t = 0 := by sorry
