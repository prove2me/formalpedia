-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_interaction_symm
-- name    : Sabidussi.CyclicWord.Word.interaction_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:36.148779+00:00
-- url     : https://prove2.me/theorems/b152d4b8-1a7f-421a-8272-6a5a109bf378
-- title:
--   Word: interaction symm
-- statement:
--   The Word construction uses the interaction symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L198-L258
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L198-L258

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

theorem Sabidussi.CyclicWord.Word.interaction_symm
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v u : V) (cv cu : Fin 3) :
    W.interaction hmin v u cv cu = W.interaction hmin u v cu cv := by sorry
