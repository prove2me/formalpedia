-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_localQuadraticContribution_eq_zero
-- name    : Sabidussi.CyclicWord.localQuadraticContribution_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:17.445107+00:00
-- url     : https://prove2.me/theorems/575a2da0-5d16-5918-bbcc-14536d08c27e
-- title:
--   Cyclic Word: local Quadratic Contribution eq zero
-- statement:
--   The recursively extended local patterns retain the quadratic cancellation of the pair and
--   triple base cases.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L95-L100
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L95-L100

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

theorem Sabidussi.CyclicWord.localQuadraticContribution_eq_zero (n : ℕ) (c : Fin 3) :
    localQuadraticContribution n c = 0 := by sorry
