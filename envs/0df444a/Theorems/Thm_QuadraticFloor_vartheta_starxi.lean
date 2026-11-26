-- Prove2me | Theorems.Thm_QuadraticFloor_vartheta_starxi
-- name    : QuadraticFloor.vartheta_starxi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:01.123943+00:00
-- url     : https://prove2.me/theorems/53e171c5-885d-56dd-adde-6b2290f27527
-- title:
--   Quadratic Floor: vartheta starxi
-- statement:
--   The Quadratic Floor construction uses the vartheta starxi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L135-L141
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L135-L141

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

theorem QuadraticFloor.vartheta_starxi : vartheta p (star xi) = fun x => starRingEnd ℂ (Theta p x) := by sorry
