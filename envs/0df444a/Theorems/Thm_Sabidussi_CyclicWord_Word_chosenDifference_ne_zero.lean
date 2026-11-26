-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_chosenDifference_ne_zero
-- name    : Sabidussi.CyclicWord.Word.chosenDifference_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:39.559649+00:00
-- url     : https://prove2.me/theorems/f414d21d-e681-4576-adb7-90321a7835bb
-- title:
--   Word: chosen Difference ne zero
-- statement:
--   The Word construction uses the chosen Difference ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L305-L309
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L305-L309

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

theorem Sabidussi.CyclicWord.Word.chosenDifference_ne_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (i : W.Pos) :
    W.chosenDifference hmin choice i ≠ 0 := by sorry
