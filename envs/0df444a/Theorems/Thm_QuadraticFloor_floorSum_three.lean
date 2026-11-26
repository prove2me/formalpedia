-- Prove2me | Theorems.Thm_QuadraticFloor_floorSum_three
-- name    : QuadraticFloor.floorSum_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:58.019788+00:00
-- url     : https://prove2.me/theorems/3e2764a5-d643-58f7-a769-1d1700457816
-- title:
--   Quadratic Floor: floor Sum three
-- statement:
--   **Theorem 4.2, Bernoulli form.** `𝒮_3(p) = 1 - (B_{1,η_p}^{(24p)} + B_{1,χ_{-24p}}^{(24p)})/2`,
--   with `η_p` induced to modulus `24p` and `χ_{-24p} = η_p χ_{-4} (·/3)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L101-L106
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L101-L106

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.floorSum_three (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      (bern (24 * p) (fun x => (eta p x : ℂ) * (if 3 ∣ x then 0 else 1)) +
        bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
          (legendreSym 3 x : ℂ))) := by sorry
