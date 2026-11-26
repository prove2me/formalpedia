-- Prove2me | Theorems.Thm_QuadraticFloor_floorSum_five
-- name    : QuadraticFloor.floorSum_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:43.128398+00:00
-- url     : https://prove2.me/theorems/68bdf463-0a06-4960-a628-13ecd845a3e8
-- title:
--   Quadratic Floor: floor Sum five
-- statement:
--   The two sums with `B = 1, 3`, each from Theorem 3.2 at `A = 5`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L187-L195
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L187-L195

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.floorSum_five (hp2 : p ≠ 2) (hp5 : p ≠ 5) {B : ℤ} (hB : Admissible 5 B 0) :
    (floorSum 5 B 0 p : ℂ) = 1 - (1 / 4) *
      ∑ ψ : DirichletCharacter ℂ 5,
        starRingEnd ℂ (ψ ((B : ZMod 5) ^ 2)) * bern (40 * p) (vartheta p ψ) := by sorry
