-- Prove2me | Theorems.Thm_QuadraticFloor_not_dvd_eight_mul
-- name    : QuadraticFloor.not_dvd_eight_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:44.616474+00:00
-- url     : https://prove2.me/theorems/9191eff9-bf17-4b2b-870d-7bc5982b45de
-- title:
--   Quadratic Floor: not dvd eight mul
-- statement:
--   The Quadratic Floor construction uses the not dvd eight mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L120-L125
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L120-L125

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.not_dvd_eight_mul (hp2 : p ≠ 2) {A : ℕ} (hpA : ¬ p ∣ A) : ¬ p ∣ 8 * A := by sorry
