-- Prove2me | Theorems.Thm_Sabidussi_sum_doubleDifference
-- name    : Sabidussi.sum_doubleDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:45.371045+00:00
-- url     : https://prove2.me/theorems/48f2f57a-6426-4729-95f9-8db0f9fd678d
-- title:
--   Sabidussi: sum double Difference
-- statement:
--   The Sabidussi construction uses the sum double Difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L137-L139
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L137-L139

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.sum_doubleDifference (t : Color) : ∑ i, doubleDifference t i = 0 := by sorry
