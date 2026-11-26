-- Prove2me | Theorems.Thm_Sabidussi_tripleDifference_two
-- name    : Sabidussi.tripleDifference_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:34.889858+00:00
-- url     : https://prove2.me/theorems/dcf5e8ca-1e35-4a50-8d22-e357ad58bc87
-- title:
--   Sabidussi: triple Difference two
-- statement:
--   The Sabidussi construction uses the triple Difference two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L103-L104
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L103-L104

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.tripleDifference_two (t : Color) :
    tripleDifference t 2 = (t.1 + t.2, t.1) := by sorry

attribute [defeq] Sabidussi.tripleDifference_two
