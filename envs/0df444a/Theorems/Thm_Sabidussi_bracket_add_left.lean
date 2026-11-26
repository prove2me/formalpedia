-- Prove2me | Theorems.Thm_Sabidussi_bracket_add_left
-- name    : Sabidussi.bracket_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:49.786748+00:00
-- url     : https://prove2.me/theorems/e2b34cb5-109d-5480-b48c-928a1a6b3e45
-- title:
--   Sabidussi: bracket add left
-- statement:
--   The Sabidussi construction uses the bracket add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L53-L56
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L53-L56

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.bracket_add_left (x y z : Color) :
    bracket (x + y) z = bracket x z + bracket y z := by sorry
