-- Prove2me | Theorems.Thm_QuadraticFloor_odd_of_ne_two
-- name    : QuadraticFloor.odd_of_ne_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:29.219178+00:00
-- url     : https://prove2.me/theorems/9c6c4cfe-e21f-564e-962d-a9597bed8bb4
-- title:
--   Quadratic Floor: odd of ne two
-- statement:
--   The Quadratic Floor construction uses the odd of ne two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L49-L49
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L49-L49

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.odd_of_ne_two (hp2 : p ≠ 2) : Odd p := by sorry
