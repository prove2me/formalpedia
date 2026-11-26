-- Prove2me | Theorems.Thm_QuadraticFloor_chi4_reflect
-- name    : QuadraticFloor.chi4_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:56.960643+00:00
-- url     : https://prove2.me/theorems/b3a36ede-787b-4ef3-a75e-e64e98bb66f2
-- title:
--   Quadratic Floor: chi4 reflect
-- statement:
--   The Quadratic Floor construction uses the chi4 reflect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L289-L293
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L289-L293

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}

theorem QuadraticFloor.chi4_reflect (A p : ℕ) {x : ℕ} (hx : x ≤ 8 * A * p) :
    ZMod.χ₄ ((8 * A * p - x : ℕ) : ZMod 4) = -ZMod.χ₄ (x : ZMod 4) := by sorry
