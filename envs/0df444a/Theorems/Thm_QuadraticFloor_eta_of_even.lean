-- Prove2me | Theorems.Thm_QuadraticFloor_eta_of_even
-- name    : QuadraticFloor.eta_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:19.579422+00:00
-- url     : https://prove2.me/theorems/964d86e1-eba1-5c63-bd3a-c16cc3f77f06
-- title:
--   Quadratic Floor: eta of even
-- statement:
--   The Quadratic Floor construction uses the eta of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L92-L92
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L92-L92

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem QuadraticFloor.eta_of_even {x : ℕ} (hx : Even x) : eta p x = 0 := by sorry
