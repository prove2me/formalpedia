-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_sum_orderedLetterInteraction
-- name    : Sabidussi.CyclicWord.Word.sum_orderedLetterInteraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:48.474921+00:00
-- url     : https://prove2.me/theorems/05496768-5f7b-4fd7-ad6e-fd6d0de757ab
-- title:
--   Word: sum ordered Letter Interaction
-- statement:
--   Partitioning earlier word positions according to their letter.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L399-L424
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L399-L424

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

theorem Sabidussi.CyclicWord.Word.sum_orderedLetterInteraction (y : W.Pos → Color) (v : V) :
    (∑ u, W.orderedLetterInteraction y v u) =
      ∑ i : W.Occurrence v, ∑ j ∈ Finset.Iio i.1, bracket (y i.1) (y j) := by sorry
