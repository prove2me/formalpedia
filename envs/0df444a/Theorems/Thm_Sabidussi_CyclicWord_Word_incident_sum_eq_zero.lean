-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_incident_sum_eq_zero
-- name    : Sabidussi.CyclicWord.Word.incident_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:52.469196+00:00
-- url     : https://prove2.me/theorems/5cf1a7a1-272d-5d5e-8a99-b327a93a4932
-- title:
--   Word: incident sum eq zero
-- statement:
--   The Word construction uses the incident sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L553-L575
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L553-L575

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

theorem Sabidussi.CyclicWord.Word.incident_sum_eq_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (v : V) :
    let y := W.chosenDifference hmin choice
    let x := W.prefixColor y
    ∑ os : W.Occurrence v × Fin 2, W.incidentColor x os.1 os.2 = 0 := by sorry
