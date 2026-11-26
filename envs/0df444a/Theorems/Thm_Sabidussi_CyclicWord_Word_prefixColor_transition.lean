-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_prefixColor_transition
-- name    : Sabidussi.CyclicWord.Word.prefixColor_transition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:24.502218+00:00
-- url     : https://prove2.me/theorems/2000b445-ceb3-5f62-a4ed-228c6b74d82d
-- title:
--   Word: prefix Color transition
-- statement:
--   The Word construction uses the prefix Color transition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L352-L375
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L352-L375

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

theorem Sabidussi.CyclicWord.Word.prefixColor_transition
    (y : W.Pos → Color) (htotal : ∑ i, y i = 0) (i : W.Pos) :
    W.prefixColor y (W.prev i) + W.prefixColor y i = y i := by sorry
