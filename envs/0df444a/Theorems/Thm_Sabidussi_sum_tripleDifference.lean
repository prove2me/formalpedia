-- Prove2me | Theorems.Thm_Sabidussi_sum_tripleDifference
-- name    : Sabidussi.sum_tripleDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:04.174851+00:00
-- url     : https://prove2.me/theorems/d9c25ca4-94c8-59bb-83fd-8c71f27b2133
-- title:
--   Sabidussi: sum triple Difference
-- statement:
--   The Sabidussi construction uses the sum triple Difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L106-L115
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L106-L115

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.sum_tripleDifference (t : Color) : ∑ i, tripleDifference t i = 0 := by sorry
