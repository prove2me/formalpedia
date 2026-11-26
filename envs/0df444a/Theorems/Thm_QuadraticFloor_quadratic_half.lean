-- Prove2me | Theorems.Thm_QuadraticFloor_quadratic_half
-- name    : QuadraticFloor.quadratic_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:03:43.700599+00:00
-- url     : https://prove2.me/theorems/2fd6e6c5-b139-4f40-b84a-d17217640687
-- title:
--   Quadratic Floor: quadratic half
-- statement:
--   **Theorem 4.4, the quadratic half, Bernoulli form.**
--   `𝒮_{5,1,0}(p) + 𝒮_{5,3,0}(p) - 2 = -(B_{1,η_p}^{(40p)} + B_{1,χ_{-40p}}^{(40p)})/2`, with `η_p`
--   induced to modulus `40p` and `χ_{-40p} = η_p (·/5)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L111-L115
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L111-L115

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.quadratic_half (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) = -(1 / 2) *
      (bern (40 * p) (fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1)) +
        bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ))) := by sorry
