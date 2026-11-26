-- Prove2me | Theorems.Thm_QuadraticFloor_cast_sub_of_dvd
-- name    : QuadraticFloor.cast_sub_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:36.744164+00:00
-- url     : https://prove2.me/theorems/19eba319-0aee-5464-93e4-4799e0830e28
-- title:
--   Quadratic Floor: cast sub of dvd
-- statement:
--   The Quadratic Floor construction uses the cast sub of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L31-L33
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L31-L33

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.cast_sub_of_dvd {q x : ℕ} (n : ℕ) (hx : x ≤ q) (h : n ∣ q) :
    ((q - x : ℕ) : ZMod n) = -(x : ZMod n) := by sorry
