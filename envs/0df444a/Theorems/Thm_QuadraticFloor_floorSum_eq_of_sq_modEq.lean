-- Prove2me | Theorems.Thm_QuadraticFloor_floorSum_eq_of_sq_modEq
-- name    : QuadraticFloor.floorSum_eq_of_sq_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:03:33.187926+00:00
-- url     : https://prove2.me/theorems/d4eefaba-84a3-44ce-b286-d9e8e323eb6a
-- title:
--   Quadratic Floor: floor Sum eq of sq mod Eq
-- statement:
--   **Corollary 3.4.** Admissible pairs with the same square class `B² mod A` give the same floor
--   sum and the same sign `(-1)^C`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L80-L84
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L80-L84

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.floorSum_eq_of_sq_modEq (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C B' C' : ℤ} (h : Admissible A B C) (h' : Admissible A B' C')
    (hBB : B ^ 2 ≡ B' ^ 2 [ZMOD A]) :
    floorSum A B C p = floorSum A B' C' p ∧ C.negOnePow = C'.negOnePow := by sorry
