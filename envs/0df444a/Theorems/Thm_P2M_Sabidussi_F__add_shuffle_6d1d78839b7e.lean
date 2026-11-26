-- Prove2me | Theorems.Thm_P2M_Sabidussi_F__add_shuffle_6d1d78839b7e
-- name    : P2M_Sabidussi_F__add_shuffle_6d1d78839b7e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:07.967847+00:00
-- url     : https://prove2.me/theorems/af056f82-751a-4597-bae4-f662c81e5219
-- title:
--   P2 M Sabidussi F  add shuffle 6d1d78839b7e: P2 M Sabidussi F  add shuffle 6d1d78839b7e
-- statement:
--   The P2 M Sabidussi F  add shuffle 6d1d78839b7e construction uses the P2 M Sabidussi F  add shuffle 6d1d78839b7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L28-L31
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L28-L31

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem P2M_Sabidussi_F__add_shuffle_6d1d78839b7e (a b : F₂) : a + (b + (a + b)) = 0 := by sorry

alias «Sabidussi».«F₂_add_shuffle» := P2M_Sabidussi_F__add_shuffle_6d1d78839b7e
