-- Prove2me | Theorems.Thm_QuadraticFloor_monic_even_bound
-- name    : QuadraticFloor.monic_even_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:04:23.623339+00:00
-- url     : https://prove2.me/theorems/063beaee-61e2-4d07-9191-221b55eecc02
-- title:
--   Quadratic Floor: monic even bound
-- statement:
--   **Theorem 7.1(2), the bound.** `|𝒮_{1,2t,b}(p)| ≤ 1 + 2|t|`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L144-L146
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L144-L146

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.monic_even_bound (hp2 : p ≠ 2) (t b : ℤ) :
    |floorSum 1 (2 * t) b p| ≤ 1 + 2 * |t| := by sorry
