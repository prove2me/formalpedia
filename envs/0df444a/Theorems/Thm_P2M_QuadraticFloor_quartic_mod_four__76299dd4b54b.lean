-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_quartic_mod_four__76299dd4b54b
-- name    : P2M_QuadraticFloor_quartic_mod_four__76299dd4b54b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:00.634036+00:00
-- url     : https://prove2.me/theorems/5ae833aa-9a5c-4c28-903f-05950b2467e0
-- title:
--   P2 M Quadratic Floor quartic mod four  76299dd4b54b: P2 M Quadratic Floor quartic mod four  76299dd4b54b
-- statement:
--   **Proposition 4.6.** `Re B_{1,Θ_p}` is an integer and `Re B_{1,Θ_p} ≡ 2 (z_1 - z_3) (mod 4)`;
--   in particular it is even.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L330-L340
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L330-L340

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_quartic_mod_four__76299dd4b54b (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ∃ m : ℤ, (bern (40 * p) (Theta p)).re = m ∧ m ≡ 2 * (zB 1 p - zB 3 p) [ZMOD 4] := by sorry

alias «QuadraticFloor».«quartic_mod_four'» := P2M_QuadraticFloor_quartic_mod_four__76299dd4b54b
