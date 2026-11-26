-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_chosen_localQuadratic
-- name    : Sabidussi.CyclicWord.Word.chosen_localQuadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:42.42725+00:00
-- url     : https://prove2.me/theorems/c173de0b-9f8b-4948-b1f5-373c48f2b674
-- title:
--   Word: chosen local Quadratic
-- statement:
--   The Word construction uses the chosen local Quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L440-L447
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L440-L447

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

theorem Sabidussi.CyclicWord.Word.chosen_localQuadratic
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (v : V) :
    (∑ i : W.Occurrence v, quadratic (W.chosenDifference hmin choice i.1)) +
      W.orderedLetterInteraction (W.chosenDifference hmin choice) v v = 0 := by sorry
