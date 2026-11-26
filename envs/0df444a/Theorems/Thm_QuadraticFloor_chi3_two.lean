-- Prove2me | Theorems.Thm_QuadraticFloor_chi3_two
-- name    : QuadraticFloor.chi3_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:31.718611+00:00
-- url     : https://prove2.me/theorems/b0d72fd3-1557-5d17-a2bd-248e7bb16b36
-- title:
--   Quadratic Floor: chi3 two
-- statement:
--   The Quadratic Floor construction uses the chi3 two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L131-L135
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L131-L135

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.chi3_two : chi3 2 = -1 := by sorry
