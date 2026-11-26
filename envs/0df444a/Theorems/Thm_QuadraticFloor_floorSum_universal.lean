-- Prove2me | Theorems.Thm_QuadraticFloor_floorSum_universal
-- name    : QuadraticFloor.floorSum_universal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:03:25.692896+00:00
-- url     : https://prove2.me/theorems/2ae9e2db-e81b-4c58-926d-96edd008d4e2
-- title:
--   Quadratic Floor: floor Sum universal
-- statement:
--   **Corollary 3.3.** `𝒮_{A,1,0}(p) = 1 - (1/φ(A)) ∑_ψ B_{1,ϑ_{p,ψ}}^{(8Ap)}`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L73-L76
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L73-L76

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.floorSum_universal (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A) :
    (floorSum A 1 0 p : ℂ) = 1 - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, bern (8 * A * p) (vartheta p ψ) := by sorry
