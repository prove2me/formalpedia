-- Prove2me | Theorems.Thm_QuadraticFloor_kap_five
-- name    : QuadraticFloor.kap_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:45.807265+00:00
-- url     : https://prove2.me/theorems/cab73611-cb8b-4469-9cbe-1d41c9ae2910
-- title:
--   Quadratic Floor: kap five
-- statement:
--   The Quadratic Floor construction uses the kap five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L31-L31
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L31-L31

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.kap_five (p : ℕ) : kap p 5 = -1 := by sorry
