-- Prove2me | Theorems.Thm_QuadraticFloor_monic_even_eventually_const
-- name    : QuadraticFloor.monic_even_eventually_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:04:13.590229+00:00
-- url     : https://prove2.me/theorems/d47782f8-fdf3-5025-9904-8945abcf0dcd
-- title:
--   Quadratic Floor: monic even eventually const
-- statement:
--   **Theorem 7.1(2), eventual constancy.** For fixed `t` and `b`, `𝒮_{1,2t,b}(p)` takes one
--   value for all sufficiently large primes `p`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L150-L152
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L150-L152

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.monic_even_eventually_const (t b : ℤ) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ p : ℕ, p.Prime → N < p → floorSum 1 (2 * t) b p = c := by sorry
