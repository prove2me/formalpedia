-- Prove2me | Theorems.Thm_QuadraticFloor_chi4_add
-- name    : QuadraticFloor.chi4_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:07.470904+00:00
-- url     : https://prove2.me/theorems/92ecfb25-130b-50dd-9cc6-4bd5f69fb49e
-- title:
--   Quadratic Floor: chi4 add
-- statement:
--   The Quadratic Floor construction uses the chi4 add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L286-L287
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L286-L287

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

theorem QuadraticFloor.chi4_add (A p x : ℕ) : ZMod.χ₄ ((x + 4 * A * p : ℕ) : ZMod 4) = ZMod.χ₄ (x : ZMod 4) := by sorry
