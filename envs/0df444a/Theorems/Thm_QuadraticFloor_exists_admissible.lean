-- Prove2me | Theorems.Thm_QuadraticFloor_exists_admissible
-- name    : QuadraticFloor.exists_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:53.443369+00:00
-- url     : https://prove2.me/theorems/5dd38a7a-f026-59a8-b9be-638d2ad4f3a0
-- title:
--   Quadratic Floor: exists admissible
-- statement:
--   **Corollary 3.4, every square class arises.**
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L87-L89
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L87-L89

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.exists_admissible {A : ℕ} (hA : Odd A) {B₀ : ℤ} (hB₀ : Int.gcd B₀ A = 1) :
    ∃ B C : ℤ, Admissible A B C ∧ B ≡ B₀ [ZMOD A] := by sorry
