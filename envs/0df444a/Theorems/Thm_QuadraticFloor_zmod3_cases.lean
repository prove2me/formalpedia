-- Prove2me | Theorems.Thm_QuadraticFloor_zmod3_cases
-- name    : QuadraticFloor.zmod3_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:43.341177+00:00
-- url     : https://prove2.me/theorems/d46f9f3c-84cc-4d1b-92db-b77367ddeb32
-- title:
--   Quadratic Floor: zmod3 cases
-- statement:
--   The Quadratic Floor construction uses the zmod3 cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L137-L137
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L137-L137

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.zmod3_cases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by sorry
