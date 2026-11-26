-- Prove2me | Theorems.Thm_QuadraticFloor_xi_sq_nat
-- name    : QuadraticFloor.xi_sq_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:09.81691+00:00
-- url     : https://prove2.me/theorems/b5dcb785-0bb5-557f-98ed-36bcdbe5b420
-- title:
--   Quadratic Floor: xi sq nat
-- statement:
--   The Quadratic Floor construction uses the xi sq nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L152-L162
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L152-L162

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.xi_sq_nat (x : ℕ) : (xi (x : ZMod 5)) ^ 2 = (jacobiSym x 5 : ℂ) := by sorry
