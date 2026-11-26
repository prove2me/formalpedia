-- Prove2me | Theorems.Thm_QuadraticFloor_psi_neg_one
-- name    : QuadraticFloor.psi_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:33.151965+00:00
-- url     : https://prove2.me/theorems/31ec7d6f-2700-458f-a40a-1eeac50ed606
-- title:
--   Quadratic Floor: psi neg one
-- statement:
--   The Quadratic Floor construction uses the psi neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L60-L61
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L60-L61

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.psi_neg_one {A : ℕ} (ψ : DirichletCharacter ℂ A) : ψ (-1) = 1 ∨ ψ (-1) = -1 := by sorry
