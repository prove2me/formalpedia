-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_window_form__e277282c21f6
-- name    : P2M_QuadraticFloor_window_form__e277282c21f6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:42.419983+00:00
-- url     : https://prove2.me/theorems/f9ae46a6-105a-4aa1-9023-ffc45da273a0
-- title:
--   P2 M Quadratic Floor window form  e277282c21f6: P2 M Quadratic Floor window form  e277282c21f6
-- statement:
--   **Lemma 2.3 (window form)**, stated with the discriminant `D = B² - 4AC` of the admissible
--   pair.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L234-L242
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L234-L242

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_window_form__e277282c21f6 (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A) {B C : ℤ}
    (hBC : Admissible A B C) :
    floorSum A B C p - (C.negOnePow : ℤ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = (B ^ 2 - 4 * A * C).toNat),
        eta p x := by sorry

alias «QuadraticFloor».«window_form'» := P2M_QuadraticFloor_window_form__e277282c21f6
