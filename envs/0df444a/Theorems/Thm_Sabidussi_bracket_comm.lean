-- Prove2me | Theorems.Thm_Sabidussi_bracket_comm
-- name    : Sabidussi.bracket_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:29.689272+00:00
-- url     : https://prove2.me/theorems/1ce42226-6a4e-5e2e-94bd-ea1a9d4876de
-- title:
--   Sabidussi: bracket comm
-- statement:
--   The Sabidussi construction uses the bracket comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L77-L78
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L77-L78

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.bracket_comm (x y : Color) : bracket x y = bracket y x := by sorry
