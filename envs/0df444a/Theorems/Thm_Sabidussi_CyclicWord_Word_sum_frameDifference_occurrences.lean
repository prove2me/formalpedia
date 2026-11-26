-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_sum_frameDifference_occurrences
-- name    : Sabidussi.CyclicWord.Word.sum_frameDifference_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:40.925911+00:00
-- url     : https://prove2.me/theorems/dedfa901-b7bb-46a3-93b3-22799d5712c1
-- title:
--   Word: sum frame Difference occurrences
-- statement:
--   The Word construction uses the sum frame Difference occurrences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L130-L135
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L130-L135

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

theorem Sabidussi.CyclicWord.Word.sum_frameDifference_occurrences
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) (v : V) (c : Fin 3) :
    ∑ o, W.frameDifference hmin v c o = 0 := by sorry
