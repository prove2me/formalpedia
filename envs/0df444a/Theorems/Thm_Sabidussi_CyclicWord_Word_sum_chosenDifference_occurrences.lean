-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_sum_chosenDifference_occurrences
-- name    : Sabidussi.CyclicWord.Word.sum_chosenDifference_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:42.574799+00:00
-- url     : https://prove2.me/theorems/f37109af-ba91-5562-b076-99b2a734a564
-- title:
--   Word: sum chosen Difference occurrences
-- statement:
--   The Word construction uses the sum chosen Difference occurrences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L319-L330
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L319-L330

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

theorem Sabidussi.CyclicWord.Word.sum_chosenDifference_occurrences
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (v : V) :
    ∑ o : W.Occurrence v, W.chosenDifference hmin choice o.1 = 0 := by sorry
