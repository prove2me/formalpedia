-- Prove2me | Theorems.Thm_QuadraticFloor_card_zero_terms
-- name    : QuadraticFloor.card_zero_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:48.809022+00:00
-- url     : https://prove2.me/theorems/0d598d78-43b1-536f-8f00-790a778b2f6f
-- title:
--   Quadratic Floor: card zero terms
-- statement:
--   The number of vanishing terms in the progression `B² + 40 j`, `0 ≤ j ≤ (p-1)/2`, is `z_B`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L253-L291
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L253-L291

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.card_zero_terms (hp2 : p ≠ 2) (hp5 : p ≠ 5) (B : ℤ) :
    (((range ((p + 1) / 2)).filter fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0).card : ℤ) =
      zB B p := by sorry
