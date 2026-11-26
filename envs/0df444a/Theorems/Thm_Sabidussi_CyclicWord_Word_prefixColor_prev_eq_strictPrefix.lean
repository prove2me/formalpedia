-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_prefixColor_prev_eq_strictPrefix
-- name    : Sabidussi.CyclicWord.Word.prefixColor_prev_eq_strictPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:44.04171+00:00
-- url     : https://prove2.me/theorems/b97e696a-7501-44f2-92f3-abd0b556557e
-- title:
--   Word: prefix Color prev eq strict Prefix
-- statement:
--   The Word construction uses the prefix Color prev eq strict Prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L377-L391
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L377-L391

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

theorem Sabidussi.CyclicWord.Word.prefixColor_prev_eq_strictPrefix
    (y : W.Pos → Color) (htotal : ∑ i, y i = 0) (i : W.Pos) :
    W.prefixColor y (W.prev i) = ∑ j ∈ Finset.Iio i, y j := by sorry
