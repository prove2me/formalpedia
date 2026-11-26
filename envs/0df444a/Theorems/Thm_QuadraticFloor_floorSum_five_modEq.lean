-- Prove2me | Theorems.Thm_QuadraticFloor_floorSum_five_modEq
-- name    : QuadraticFloor.floorSum_five_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:53.709217+00:00
-- url     : https://prove2.me/theorems/d86aa87d-3008-5bb7-b5b6-e47dec88479a
-- title:
--   Quadratic Floor: floor Sum five mod Eq
-- statement:
--   `𝒮_{5,B,0}(p) - 1 ≡ 2((p+1)/2 - z_B) (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L294-L326
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L294-L326

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.floorSum_five_modEq (hp2 : p ≠ 2) (hp5 : p ≠ 5) {B : ℤ} (hB : Odd B) :
    floorSum 5 B 0 p - 1 ≡ 2 * (((p + 1) / 2 : ℕ) - zB B p) [ZMOD 4] := by sorry
