-- Prove2me | Theorems.Thm_Sabidussi_tripleDifference_ne_zero
-- name    : Sabidussi.tripleDifference_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:10.539809+00:00
-- url     : https://prove2.me/theorems/b472cfe5-8326-4e45-a06a-a714b4be9246
-- title:
--   Sabidussi: triple Difference ne zero
-- statement:
--   The Sabidussi construction uses the triple Difference ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L117-L132
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L117-L132

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.tripleDifference_ne_zero (t : Color) (ht : t ≠ 0) (i : Fin 3) :
    tripleDifference t i ≠ 0 := by sorry
