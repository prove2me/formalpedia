-- Prove2me | Theorems.Thm_QuadraticFloor_vartheta_xi
-- name    : QuadraticFloor.vartheta_xi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:30.961955+00:00
-- url     : https://prove2.me/theorems/1c1f01b4-336d-4eab-8c28-7c4c9031c906
-- title:
--   Quadratic Floor: vartheta xi
-- statement:
--   The Quadratic Floor construction uses the vartheta xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L128-L132
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L128-L132

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

theorem QuadraticFloor.vartheta_xi : vartheta p xi = Theta p := by sorry
