-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_window__8c99d9986259
-- name    : P2M_QuadraticFloor_window__8c99d9986259
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:16.090805+00:00
-- url     : https://prove2.me/theorems/c1f833df-e5c7-4e57-8002-529169722716
-- title:
--   P2 M Quadratic Floor window  8c99d9986259: P2 M Quadratic Floor window  8c99d9986259
-- statement:
--   **Lemma 2.3 (window form).** `𝒮_{A,B,C}(p) - (-1)^C = 2 ∑ η_p(x)` over the `x ∈ [1, 4Ap]`
--   with `x ≡ D (mod 8A)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L173-L230
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L173-L230

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_window__8c99d9986259 (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A) {B C : ℤ}
    (hBC : Admissible A B C) {d : ℕ} (hdD : (d : ℤ) = B ^ 2 - 4 * A * C) (hd4A : d < 4 * A)
    (hd8 : d % 8 = if Even C then 1 else 5) :
    floorSum A B C p - (C.negOnePow : ℤ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), eta p x := by sorry

alias «QuadraticFloor».«window'» := P2M_QuadraticFloor_window__8c99d9986259
