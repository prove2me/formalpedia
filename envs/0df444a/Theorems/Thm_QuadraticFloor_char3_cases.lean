-- Prove2me | Theorems.Thm_QuadraticFloor_char3_cases
-- name    : QuadraticFloor.char3_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:23.897942+00:00
-- url     : https://prove2.me/theorems/96db2704-0f31-4305-b266-2b4e8c471030
-- title:
--   Quadratic Floor: char3 cases
-- statement:
--   The Quadratic Floor construction uses the char3 cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L139-L158
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Corollaries.lean#L139-L158

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.char3_cases (ψ : DirichletCharacter ℂ 3) : ψ = 1 ∨ ψ = chi3 := by sorry
