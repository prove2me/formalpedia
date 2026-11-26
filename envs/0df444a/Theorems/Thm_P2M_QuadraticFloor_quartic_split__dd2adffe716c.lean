-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_quartic_split__dd2adffe716c
-- name    : P2M_QuadraticFloor_quartic_split__dd2adffe716c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:29.825326+00:00
-- url     : https://prove2.me/theorems/7c40d86b-c930-4221-bc20-e86744c73ea1
-- title:
--   P2 M Quadratic Floor quartic split  dd2adffe716c: P2 M Quadratic Floor quartic split  dd2adffe716c
-- statement:
--   **Corollary 4.5, the quartic coordinate.** `Re B_{1,Θ_p} = 𝒮_{5,3,0}(p) - 𝒮_{5,1,0}(p)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L198-L217
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L198-L217

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_quartic_split__dd2adffe716c (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 3 0 p - floorSum 5 1 0 p : ℤ) : ℝ) = (bern (40 * p) (Theta p)).re := by sorry

alias «QuadraticFloor».«quartic_split'» := P2M_QuadraticFloor_quartic_split__dd2adffe716c
