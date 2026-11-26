-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_exists_coloring
-- name    : Sabidussi.CyclicWord.Word.exists_coloring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:10.019999+00:00
-- url     : https://prove2.me/theorems/6128d2e5-40f4-57cb-87ac-ad5326c386cf
-- title:
--   Word: exists coloring
-- statement:
--   Every nonempty cyclic word in which each letter occurs at least twice has the required
--   four-colouring of its gaps.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L579-L605
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L579-L605

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

theorem Sabidussi.CyclicWord.Word.exists_coloring
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) : Nonempty W.Coloring := by sorry
