-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_quadratic_incident_sum_eq_zero
-- name    : Sabidussi.CyclicWord.Word.quadratic_incident_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:07.389077+00:00
-- url     : https://prove2.me/theorems/9d65acf1-4c45-5fc2-aff2-26bfb6f6a09c
-- title:
--   Word: quadratic incident sum eq zero
-- statement:
--   The balanced interaction equations are exactly the missing quadratic moment at each letter.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L493-L551
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L493-L551

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

theorem Sabidussi.CyclicWord.Word.quadratic_incident_sum_eq_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3)
    (hbalanced : ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0)
    (v : V) :
    let y := W.chosenDifference hmin choice
    let x := W.prefixColor y
    ∑ os : W.Occurrence v × Fin 2, quadratic (W.incidentColor x os.1 os.2) = 0 := by sorry
