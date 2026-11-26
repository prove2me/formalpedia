-- Prove2me | Theorems.Thm_Sabidussi_double_local_quadratic
-- name    : Sabidussi.double_local_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:29.707328+00:00
-- url     : https://prove2.me/theorems/b504f809-2dd1-559c-a988-c8d1b8dab6f6
-- title:
--   Sabidussi: double local quadratic
-- statement:
--   The local quadratic contribution from two equal nonzero differences vanishes.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L146-L154
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L146-L154

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.double_local_quadratic (t : Color) :
    (∑ i, quadratic (doubleDifference t i)) +
      (∑ i, ∑ j,
        if j < i then bracket (doubleDifference t i) (doubleDifference t j) else 0) = 0 := by sorry
