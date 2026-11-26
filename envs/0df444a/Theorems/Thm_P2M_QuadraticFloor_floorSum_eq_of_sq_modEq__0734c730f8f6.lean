-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_floorSum_eq_of_sq_modEq__0734c730f8f6
-- name    : P2M_QuadraticFloor_floorSum_eq_of_sq_modEq__0734c730f8f6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:06.732941+00:00
-- url     : https://prove2.me/theorems/345f2b11-4119-4967-81a5-65c53c6a7e60
-- title:
--   P2 M Quadratic Floor floor Sum eq of sq mod Eq  0734c730f8f6: P2 M Quadratic Floor floor Sum eq of sq mod Eq  0734c730f8f6
-- statement:
--   **Corollary 3.4.** Two admissible pairs with the same square class `B² mod A` give the same
--   floor sum and the same sign `(-1)^C`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L29-L61
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L29-L61

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_floorSum_eq_of_sq_modEq__0734c730f8f6 (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C B' C' : ℤ} (h : Admissible A B C) (h' : Admissible A B' C')
    (hBB : B ^ 2 ≡ B' ^ 2 [ZMOD A]) :
    floorSum A B C p = floorSum A B' C' p ∧ C.negOnePow = C'.negOnePow := by sorry

alias «QuadraticFloor».«floorSum_eq_of_sq_modEq'» := P2M_QuadraticFloor_floorSum_eq_of_sq_modEq__0734c730f8f6
