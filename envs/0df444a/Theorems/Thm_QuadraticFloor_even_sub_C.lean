-- Prove2me | Theorems.Thm_QuadraticFloor_even_sub_C
-- name    : QuadraticFloor.even_sub_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:27.170773+00:00
-- url     : https://prove2.me/theorems/d1d3b5a7-d677-48e3-9930-a3419eb8edc0
-- title:
--   Quadratic Floor: even sub C
-- statement:
--   `A n² + B n + C ≡ C (mod 2)` when `A + B` is even.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L76-L82
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L76-L82

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.even_sub_C {A B : ℤ} (hAB : Even (A + B)) (n C : ℤ) : Even (A * n ^ 2 + B * n + C - C) := by sorry
