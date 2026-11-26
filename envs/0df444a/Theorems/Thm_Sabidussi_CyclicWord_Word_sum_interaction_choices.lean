-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_sum_interaction_choices
-- name    : Sabidussi.CyclicWord.Word.sum_interaction_choices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:28.06983+00:00
-- url     : https://prove2.me/theorems/463d9113-f48e-56e1-980f-cb6566026073
-- title:
--   Word: sum interaction choices
-- statement:
--   The Word construction uses the sum interaction choices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L260-L282
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L260-L282

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

theorem Sabidussi.CyclicWord.Word.sum_interaction_choices
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v u : V) (cv : Fin 3) :
    ∑ cu, W.interaction hmin v u cv cu = 0 := by sorry
