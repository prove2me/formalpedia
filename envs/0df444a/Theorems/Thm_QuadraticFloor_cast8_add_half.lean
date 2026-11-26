-- Prove2me | Theorems.Thm_QuadraticFloor_cast8_add_half
-- name    : QuadraticFloor.cast8_add_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:40.477372+00:00
-- url     : https://prove2.me/theorems/31f381fc-1916-5675-8e99-c852ca41a852
-- title:
--   Quadratic Floor: cast8 add half
-- statement:
--   The Quadratic Floor construction uses the cast8 add half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L35-L43
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L35-L43

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.cast8_add_half {A p : ℕ} (hAp : Odd (A * p)) (x : ℕ) :
    ((x + 4 * A * p : ℕ) : ZMod 8) = (x : ZMod 8) + 4 := by sorry
