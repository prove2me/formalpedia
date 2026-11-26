-- Prove2me | Theorems.Thm_QuadraticFloor_window_form
-- name    : QuadraticFloor.window_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:04.843829+00:00
-- url     : https://prove2.me/theorems/a1385b35-f8d3-4558-ac39-e71fd235f443
-- title:
--   Quadratic Floor: window form
-- statement:
--   **Lemma 2.3 (window form).** For an admissible pair, `𝒮_{A,B,C}(p) - (-1)^C` is twice the sum
--   of `η_p(x)` over the `x ∈ [1, 4Ap]` with `x ≡ B² - 4AC (mod 8A)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L37-L42
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L37-L42

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.window_form (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A) {B C : ℤ}
    (hBC : Admissible A B C) :
    floorSum A B C p - (C.negOnePow : ℤ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = (B ^ 2 - 4 * A * C).toNat),
        eta p x := by sorry
