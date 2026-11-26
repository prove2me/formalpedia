-- Prove2me | Theorems.Thm_QuadraticFloor_square_class_decomposition
-- name    : QuadraticFloor.square_class_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:26.080988+00:00
-- url     : https://prove2.me/theorems/e3b72d32-ee34-5f25-9dbe-d835e092e67b
-- title:
--   Quadratic Floor: square class decomposition
-- statement:
--   **Theorem 3.2 (square-class decomposition).** For an admissible pair `(B, C)`,
--   `𝒮_{A,B,C}(p) = (-1)^C - (1/φ(A)) ∑_{ψ mod A} conj(ψ(B))² B_{1,ϑ_{p,ψ}}^{(8Ap)}`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L65-L70
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L65-L70

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.square_class_decomposition (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A)
    (hpA : ¬ p ∣ A) {B C : ℤ} (hBC : Admissible A B C) :
    (floorSum A B C p : ℂ) = (C.negOnePow : ℤ) - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 *
        bern (8 * A * p) (vartheta p ψ) := by sorry
