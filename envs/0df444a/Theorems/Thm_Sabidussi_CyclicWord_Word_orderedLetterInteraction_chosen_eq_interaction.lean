-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_orderedLetterInteraction_chosen_eq_interaction
-- name    : Sabidussi.CyclicWord.Word.orderedLetterInteraction_chosen_eq_interaction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:40.277946+00:00
-- url     : https://prove2.me/theorems/10094ed0-92be-5e7b-9066-f4b32ffc28af
-- title:
--   Word: ordered Letter Interaction chosen eq interaction
-- statement:
--   The Word construction uses the ordered Letter Interaction chosen eq interaction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L426-L438
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L426-L438

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

theorem Sabidussi.CyclicWord.Word.orderedLetterInteraction_chosen_eq_interaction
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) {v u : V} (hvu : v ≠ u) :
    W.orderedLetterInteraction (W.chosenDifference hmin choice) v u =
      W.interaction hmin v u (choice v) (choice u) := by sorry
