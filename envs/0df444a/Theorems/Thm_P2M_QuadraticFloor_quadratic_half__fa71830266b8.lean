-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_quadratic_half__fa71830266b8
-- name    : P2M_QuadraticFloor_quadratic_half__fa71830266b8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:41.055404+00:00
-- url     : https://prove2.me/theorems/dc9490ce-fa1b-5c3f-87b3-b2c4f227e7d3
-- title:
--   P2 M Quadratic Floor quadratic half  fa71830266b8: P2 M Quadratic Floor quadratic half  fa71830266b8
-- statement:
--   **Theorem 4.4, the quadratic half (Bernoulli form).**
--   `𝒮_{5,1,0}(p) + 𝒮_{5,3,0}(p) - 2 = -(B_{1,η_p}^{(40p)} + B_{1,χ_{-40p}}^{(40p)})/2`, where `η_p` is
--   induced to modulus `40p` and `χ_{-40p} = η_p (·/5)`. By Dirichlet's class number formula the right
--   side is `h(-40p)/2 + (1 + (p/5)) h(-8p)/2`, which is not formalized.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L223-L237
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L223-L237

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_quadratic_half__fa71830266b8 (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) = -(1 / 2) *
      (bern (40 * p) (fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1)) +
        bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ))) := by sorry

alias «QuadraticFloor».«quadratic_half'» := P2M_QuadraticFloor_quadratic_half__fa71830266b8
