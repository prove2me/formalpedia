-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_monic_even_eventually_const__f9067cd031a4
-- name    : P2M_QuadraticFloor_monic_even_eventually_const__f9067cd031a4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:22.602812+00:00
-- url     : https://prove2.me/theorems/62a458fc-c6c1-4e06-8a11-7189738cb244
-- title:
--   P2 M Quadratic Floor monic even eventually const  f9067cd031a4: P2 M Quadratic Floor monic even eventually const  f9067cd031a4
-- statement:
--   **Theorem 7.1(2), eventual constancy.** For fixed `t` and `b`, the sum `𝒮_{2t,b}(p)` takes one
--   value for all sufficiently large primes `p`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L345-L369
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L345-L369

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_monic_even_eventually_const__f9067cd031a4 (t b : ℤ) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ p : ℕ, p.Prime → N < p → floorSum 1 (2 * t) b p = c := by sorry

alias «QuadraticFloor».«monic_even_eventually_const'» := P2M_QuadraticFloor_monic_even_eventually_const__f9067cd031a4
