-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_frameDifference_localQuadratic
-- name    : Sabidussi.CyclicWord.Word.frameDifference_localQuadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:24.945959+00:00
-- url     : https://prove2.me/theorems/2d559734-ef95-4d08-a164-73d0ebd4c29c
-- title:
--   Word: frame Difference local Quadratic
-- statement:
--   The Word construction uses the frame Difference local Quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L143-L179
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L143-L179

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

theorem Sabidussi.CyclicWord.Word.frameDifference_localQuadratic
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) (v : V) (c : Fin 3) :
    (∑ o, quadratic (W.frameDifference hmin v c o)) +
      (∑ o, ∑ p,
        if p.1 < o.1 then
          bracket (W.frameDifference hmin v c o) (W.frameDifference hmin v c p)
        else 0) = 0 := by sorry
