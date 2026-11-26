-- Prove2me | Theorems.Thm_Sabidussi_tripleDifference_one
-- name    : Sabidussi.tripleDifference_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:33.063839+00:00
-- url     : https://prove2.me/theorems/daee02bf-f732-4b9c-b7e8-e25483a7b5b4
-- title:
--   Sabidussi: triple Difference one
-- statement:
--   The Sabidussi construction uses the triple Difference one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L99-L100
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L99-L100

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.tripleDifference_one (t : Color) :
    tripleDifference t 1 = (t.2, t.1 + t.2) := by sorry

attribute [defeq] Sabidussi.tripleDifference_one
