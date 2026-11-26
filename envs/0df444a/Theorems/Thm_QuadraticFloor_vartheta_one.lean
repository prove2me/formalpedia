-- Prove2me | Theorems.Thm_QuadraticFloor_vartheta_one
-- name    : QuadraticFloor.vartheta_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:30.319784+00:00
-- url     : https://prove2.me/theorems/5532b676-d6bc-497e-8626-9cf5fbc16066
-- title:
--   Quadratic Floor: vartheta one
-- statement:
--   The Quadratic Floor construction uses the vartheta one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L165-L171
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L165-L171

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem QuadraticFloor.vartheta_one : vartheta p (1 : DirichletCharacter ℂ 5) =
    fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1) := by sorry
