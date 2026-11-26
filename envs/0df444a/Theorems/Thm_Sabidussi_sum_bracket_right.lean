-- Prove2me | Theorems.Thm_Sabidussi_sum_bracket_right
-- name    : Sabidussi.sum_bracket_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:32.097728+00:00
-- url     : https://prove2.me/theorems/3d8b52bf-eee6-5eb0-a4f0-e543de5f22b0
-- title:
--   Sabidussi: sum bracket right
-- statement:
--   The Sabidussi construction uses the sum bracket right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L72-L75
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L72-L75

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.sum_bracket_right {I : Type*} [Fintype I] (x : Color) (f : I → Color) :
    ∑ i, bracket x (f i) = bracket x (∑ i, f i) := by sorry
