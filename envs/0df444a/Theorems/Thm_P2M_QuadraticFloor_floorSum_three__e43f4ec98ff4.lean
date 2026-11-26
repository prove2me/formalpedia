-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_floorSum_three__e43f4ec98ff4
-- name    : P2M_QuadraticFloor_floorSum_three__e43f4ec98ff4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:20.711625+00:00
-- url     : https://prove2.me/theorems/53c2c8f8-ce22-542b-8555-48a33b5cf04e
-- title:
--   P2 M Quadratic Floor floor Sum three  e43f4ec98ff4: P2 M Quadratic Floor floor Sum three  e43f4ec98ff4
-- statement:
--   **Theorem 4.2, Bernoulli form.**
--   `𝒮_3(p) = 1 - (B_{1,η_p}^{(24p)} + B_{1,χ_{-24p}}^{(24p)})/2`, where `η_p` is induced to modulus
--   `24p` (it vanishes on multiples of `3`) and `χ_{-24p} = η_p χ_{-4} (·/3)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L163-L198
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L163-L198

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_floorSum_three__e43f4ec98ff4 (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      (bern (24 * p) (fun x => (eta p x : ℂ) * (if 3 ∣ x then 0 else 1)) +
        bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
          (legendreSym 3 x : ℂ))) := by sorry

alias «QuadraticFloor».«floorSum_three'» := P2M_QuadraticFloor_floorSum_three__e43f4ec98ff4
