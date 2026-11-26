-- Prove2me | Theorems.Thm_QuadraticFloor_eta_of_dvd
-- name    : QuadraticFloor.eta_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:10.603607+00:00
-- url     : https://prove2.me/theorems/9a53adc5-572e-5417-bd6a-7e139b6ff781
-- title:
--   Quadratic Floor: eta of dvd
-- statement:
--   The Quadratic Floor construction uses the eta of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L94-L96
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L94-L96

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.eta_of_dvd (hp2 : p ≠ 2) {x : ℕ} (hx : p ∣ x) : eta p x = 0 := by sorry
