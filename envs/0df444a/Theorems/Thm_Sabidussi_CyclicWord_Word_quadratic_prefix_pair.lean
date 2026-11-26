-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_quadratic_prefix_pair
-- name    : Sabidussi.CyclicWord.Word.quadratic_prefix_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:04.748252+00:00
-- url     : https://prove2.me/theorems/d8b61023-cb8a-52e9-ba29-9b5cfd8a4b65
-- title:
--   Word: quadratic prefix pair
-- statement:
--   The Word construction uses the quadratic prefix pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L468-L490
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L468-L490

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
open Sabidussi.CyclicWord.Word
variable (W : Word (V := V))

theorem Sabidussi.CyclicWord.Word.quadratic_prefix_pair
    (y : W.Pos → Color) (htotal : ∑ i, y i = 0) (i : W.Pos) :
    quadratic (W.prefixColor y (W.prev i)) + quadratic (W.prefixColor y i) =
      quadratic (y i) + bracket (y i) (W.prefixColor y (W.prev i)) := by sorry
