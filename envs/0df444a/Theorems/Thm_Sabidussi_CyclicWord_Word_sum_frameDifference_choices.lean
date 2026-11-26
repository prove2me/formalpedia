-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_sum_frameDifference_choices
-- name    : Sabidussi.CyclicWord.Word.sum_frameDifference_choices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:24.289061+00:00
-- url     : https://prove2.me/theorems/7890809d-faf1-5273-9ae8-cc7d5d10258a
-- title:
--   Word: sum frame Difference choices
-- statement:
--   The Word construction uses the sum frame Difference choices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L137-L141
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L137-L141

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

theorem Sabidussi.CyclicWord.Word.sum_frameDifference_choices
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v : V) (o : W.Occurrence v) :
    ∑ c, W.frameDifference hmin v c o = 0 := by sorry
