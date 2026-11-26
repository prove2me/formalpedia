-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_floorSum_universal__ec9587aa8f07
-- name    : P2M_QuadraticFloor_floorSum_universal__ec9587aa8f07
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:54.580497+00:00
-- url     : https://prove2.me/theorems/2c7d2115-e014-4aa6-90b2-0973e7a9d676
-- title:
--   P2 M Quadratic Floor floor Sum universal  ec9587aa8f07: P2 M Quadratic Floor floor Sum universal  ec9587aa8f07
-- statement:
--   **Corollary 3.3.** `𝒮_A(p) = 1 - (1/φ(A)) ∑_ψ B_{1,ϑ_{p,ψ}}^{(8Ap)}`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L94-L100
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L94-L100

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_floorSum_universal__ec9587aa8f07 (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A) :
    (floorSum A 1 0 p : ℂ) = 1 - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, bern (8 * A * p) (vartheta p ψ) := by sorry

alias «QuadraticFloor».«floorSum_universal'» := P2M_QuadraticFloor_floorSum_universal__ec9587aa8f07
