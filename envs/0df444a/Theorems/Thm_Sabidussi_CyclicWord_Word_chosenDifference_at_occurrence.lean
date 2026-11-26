-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_chosenDifference_at_occurrence
-- name    : Sabidussi.CyclicWord.Word.chosenDifference_at_occurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:46.297933+00:00
-- url     : https://prove2.me/theorems/b17bb98f-12c1-4bb2-a5fc-5c8e562123ba
-- title:
--   Word: chosen Difference at occurrence
-- statement:
--   The Word construction uses the chosen Difference at occurrence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L311-L317
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L311-L317

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

theorem Sabidussi.CyclicWord.Word.chosenDifference_at_occurrence
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (v : V) (o : W.Occurrence v) :
    W.chosenDifference hmin choice o.1 = W.frameDifference hmin v (choice v) o := by sorry
