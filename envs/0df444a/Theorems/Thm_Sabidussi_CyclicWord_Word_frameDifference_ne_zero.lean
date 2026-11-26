-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_frameDifference_ne_zero
-- name    : Sabidussi.CyclicWord.Word.frameDifference_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:36.958025+00:00
-- url     : https://prove2.me/theorems/5db1ca03-ad3d-43ed-a9d8-f46b47a0a8a4
-- title:
--   Word: frame Difference ne zero
-- statement:
--   The Word construction uses the frame Difference ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L124-L128
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L124-L128

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

theorem Sabidussi.CyclicWord.Word.frameDifference_ne_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v : V) (c : Fin 3) (o : W.Occurrence v) :
    W.frameDifference hmin v c o ≠ 0 := by sorry
