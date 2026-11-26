-- Prove2me | Theorems.Thm_QuadraticFloor_admissible_five_three
-- name    : QuadraticFloor.admissible_five_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:51.812797+00:00
-- url     : https://prove2.me/theorems/d497398a-6025-5cf0-83c4-24e731c6a5e3
-- title:
--   Quadratic Floor: admissible five three
-- statement:
--   The Quadratic Floor construction uses the admissible five three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L184-L184
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L184-L184

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.admissible_five_three : Admissible 5 3 0 := by sorry
