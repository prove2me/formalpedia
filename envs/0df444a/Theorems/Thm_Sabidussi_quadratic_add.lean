-- Prove2me | Theorems.Thm_Sabidussi_quadratic_add
-- name    : Sabidussi.quadratic_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:34.005351+00:00
-- url     : https://prove2.me/theorems/813c0992-ec6c-5095-bd98-80b9cdc01bf0
-- title:
--   Sabidussi: quadratic add
-- statement:
--   The Sabidussi construction uses the quadratic add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L84-L87
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L84-L87

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.quadratic_add (x y : Color) :
    quadratic (x + y) = quadratic x + quadratic y + bracket x y := by sorry
