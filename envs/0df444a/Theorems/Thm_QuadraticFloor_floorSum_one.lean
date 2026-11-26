-- Prove2me | Theorems.Thm_QuadraticFloor_floorSum_one
-- name    : QuadraticFloor.floorSum_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:03:41.019032+00:00
-- url     : https://prove2.me/theorems/5aca6b29-8ff8-44cb-9958-979e2c3a9b20
-- title:
--   Quadratic Floor: floor Sum one
-- statement:
--   **Theorem 4.1, Bernoulli form.** `𝒮_1(p) = ∑_{n<p} (-1)^{⌊n(n+1)/p⌋} = 1 - B_{1,η_p}^{(8p)}`
--   (which is `1 + h(-8p)` by Dirichlet's class number formula).
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L95-L97
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L95-L97

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.floorSum_one (hp2 : p ≠ 2) :
    (floorSum 1 1 0 p : ℂ) = 1 - bern (8 * p) (fun x => (eta p x : ℂ)) := by sorry
