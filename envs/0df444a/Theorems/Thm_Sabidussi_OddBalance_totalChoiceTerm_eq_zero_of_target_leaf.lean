-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_eq_zero_of_target_leaf
-- name    : Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_target_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:13:13.939642+00:00
-- url     : https://prove2.me/theorems/e9b9e4b8-2d18-507b-bb02-d6e90f6fcfbc
-- title:
--   Odd Balance: total Choice Term eq zero of target leaf
-- statement:
--   The Odd Balance construction uses the total Choice Term eq zero of target leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L174-L203
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L174-L203

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_target_leaf
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (f : Choice S) (v₀ : {v // v ∈ S}) (w : V)
    (hw : (f v₀ : V) = w) (hnotSource : ∀ v, (v : V) ≠ w)
    (huniqueTarget : ∀ v, (f v : V) = w → v = v₀) :
    totalChoiceTerm b S f = 0 := by sorry
