-- Prove2me | Theorems.Thm_QuadraticFloor_cast_add_of_dvd
-- name    : QuadraticFloor.cast_add_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:18.956121+00:00
-- url     : https://prove2.me/theorems/339802e2-f04e-58ca-8f0d-6c5a2437690f
-- title:
--   Quadratic Floor: cast add of dvd
-- statement:
--   The Quadratic Floor construction uses the cast add of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L28-L29
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L28-L29

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.cast_add_of_dvd (x m n : ℕ) (h : n ∣ m) : ((x + m : ℕ) : ZMod n) = x := by sorry
