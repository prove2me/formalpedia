-- Prove2me | Theorems.Thm_Sabidussi_doubleDifference_ne_zero
-- name    : Sabidussi.doubleDifference_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:47.6018+00:00
-- url     : https://prove2.me/theorems/0d538d75-f5eb-5cf8-ab71-64c077ceb2e9
-- title:
--   Sabidussi: double Difference ne zero
-- statement:
--   The Sabidussi construction uses the double Difference ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L141-L143
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L141-L143

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.doubleDifference_ne_zero (t : Color) (ht : t ≠ 0) (i : Fin 2) :
    doubleDifference t i ≠ 0 := by sorry
