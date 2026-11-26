-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_floorSum_one__50c18f664e37
-- name    : P2M_QuadraticFloor_floorSum_one__50c18f664e37
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:13.622158+00:00
-- url     : https://prove2.me/theorems/deacbb81-6d38-40cc-a449-6fbc9611332f
-- title:
--   P2 M Quadratic Floor floor Sum one  50c18f664e37: P2 M Quadratic Floor floor Sum one  50c18f664e37
-- statement:
--   **Theorem 4.1, Bernoulli form.** `𝒮_1(p) = ∑_{n<p} (-1)^{⌊n(n+1)/p⌋} = 1 - B_{1,η_p}^{(8p)}`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L105-L120
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L105-L120

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_floorSum_one__50c18f664e37 (hp2 : p ≠ 2) :
    (floorSum 1 1 0 p : ℂ) = 1 - bern (8 * p) (fun x => (eta p x : ℂ)) := by sorry

alias «QuadraticFloor».«floorSum_one'» := P2M_QuadraticFloor_floorSum_one__50c18f664e37
