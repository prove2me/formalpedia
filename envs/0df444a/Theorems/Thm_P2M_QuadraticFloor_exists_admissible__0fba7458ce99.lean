-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_exists_admissible__0fba7458ce99
-- name    : P2M_QuadraticFloor_exists_admissible__0fba7458ce99
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:08.286954+00:00
-- url     : https://prove2.me/theorems/db4e312c-3d1d-5df2-ba74-8c6f51b3cb09
-- title:
--   P2 M Quadratic Floor exists admissible  0fba7458ce99: P2 M Quadratic Floor exists admissible  0fba7458ce99
-- statement:
--   **Corollary 3.4, every square class arises.** For every `B₀` prime to `A` there is an admissible
--   pair `(B, C)` with `B ≡ B₀ (mod A)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L65-L89
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L65-L89

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_exists_admissible__0fba7458ce99 {A : ℕ} (hA : Odd A) {B₀ : ℤ} (hB₀ : Int.gcd B₀ A = 1) :
    ∃ B C : ℤ, Admissible A B C ∧ B ≡ B₀ [ZMOD A] := by sorry

alias «QuadraticFloor».«exists_admissible'» := P2M_QuadraticFloor_exists_admissible__0fba7458ce99
