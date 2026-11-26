-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_monic_even_bound__299c38c9066e
-- name    : P2M_QuadraticFloor_monic_even_bound__299c38c9066e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:49.603243+00:00
-- url     : https://prove2.me/theorems/949db068-ed2d-591b-be99-3d9fda1a2eef
-- title:
--   P2 M Quadratic Floor monic even bound  299c38c9066e: P2 M Quadratic Floor monic even bound  299c38c9066e
-- statement:
--   **Theorem 7.1(2), the bound.** `|𝒮_{2t,b}(p)| ≤ 1 + 2|t|`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L313-L324
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L313-L324

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_monic_even_bound__299c38c9066e (hp2 : p ≠ 2) (t b : ℤ) :
    |floorSum 1 (2 * t) b p| ≤ 1 + 2 * |t| := by sorry

alias «QuadraticFloor».«monic_even_bound'» := P2M_QuadraticFloor_monic_even_bound__299c38c9066e
