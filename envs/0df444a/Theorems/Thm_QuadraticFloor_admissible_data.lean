-- Prove2me | Theorems.Thm_QuadraticFloor_admissible_data
-- name    : QuadraticFloor.admissible_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:00.673426+00:00
-- url     : https://prove2.me/theorems/1c121843-b377-4b14-afa4-c41dc892c1ac
-- title:
--   Quadratic Floor: admissible data
-- statement:
--   The discriminant `D = B² - 4AC` of an admissible pair, as a natural number, and its
--   properties.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L129-L151
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L129-L151

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.admissible_data {A : ℕ} (hA : Odd A) {B C : ℤ} (hBC : Admissible A B C) :
    ∃ d : ℕ, (d : ℤ) = B ^ 2 - 4 * A * C ∧ 1 ≤ d ∧ d < 4 * A ∧ d % 4 = 1 ∧
      (d % 8 = if Even C then 1 else 5) := by sorry
