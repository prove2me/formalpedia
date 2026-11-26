-- Prove2me | Theorems.Thm_QuadraticFloor_psi_reflect
-- name    : QuadraticFloor.psi_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:06.927306+00:00
-- url     : https://prove2.me/theorems/72cf94fd-c508-4922-a687-1bcf334e81f4
-- title:
--   Quadratic Floor: psi reflect
-- statement:
--   The Quadratic Floor construction uses the psi reflect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L63-L65
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L63-L65

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.psi_reflect {A : ℕ} (ψ : DirichletCharacter ℂ A) {q x : ℕ} (hx : x ≤ q) (hq : A ∣ q) :
    ψ ((q - x : ℕ) : ZMod A) = ψ (-1) * ψ (x : ZMod A) := by sorry
