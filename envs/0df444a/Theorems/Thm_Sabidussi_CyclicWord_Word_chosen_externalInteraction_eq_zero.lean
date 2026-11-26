-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_chosen_externalInteraction_eq_zero
-- name    : Sabidussi.CyclicWord.Word.chosen_externalInteraction_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:45.892451+00:00
-- url     : https://prove2.me/theorems/590f8608-6eac-5ea3-aad9-e4c68ac974d0
-- title:
--   Word: chosen external Interaction eq zero
-- statement:
--   The Word construction uses the chosen external Interaction eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L449-L466
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L449-L466

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

theorem Sabidussi.CyclicWord.Word.chosen_externalInteraction_eq_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3)
    (hbalanced : ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0)
    (v : V) :
    ∑ u ∈ Finset.univ.erase v,
      W.orderedLetterInteraction (W.chosenDifference hmin choice) v u = 0 := by sorry
