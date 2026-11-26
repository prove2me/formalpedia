-- Prove2me | Theorems.Thm_Sabidussi_triple_local_quadratic
-- name    : Sabidussi.triple_local_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:33.685504+00:00
-- url     : https://prove2.me/theorems/c86d2394-1f00-556c-8e0e-ffac8401d66b
-- title:
--   Sabidussi: triple local quadratic
-- statement:
--   The local quadratic contribution from the three `tripleDifference`s vanishes.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L157-L166
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L157-L166

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.triple_local_quadratic (t : Color) :
    (∑ i, quadratic (tripleDifference t i)) +
      (∑ i, ∑ j,
        if j < i then bracket (tripleDifference t i) (tripleDifference t j) else 0) = 0 := by sorry
