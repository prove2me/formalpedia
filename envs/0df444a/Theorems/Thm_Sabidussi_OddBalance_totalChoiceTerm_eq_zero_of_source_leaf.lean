-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_eq_zero_of_source_leaf
-- name    : Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_source_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:40.031543+00:00
-- url     : https://prove2.me/theorems/614240fc-e4f7-5c40-98fe-9df4ab14449a
-- title:
--   Odd Balance: total Choice Term eq zero of source leaf
-- statement:
--   The Odd Balance construction uses the total Choice Term eq zero of source leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L133-L172
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L133-L172

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

theorem Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_source_leaf
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (f : Choice S) (v₀ : {v // v ∈ S}) (w : V)
    (hw : (v₀ : V) = w) (hnotTarget : ∀ v, (f v : V) ≠ w) :
    totalChoiceTerm b S f = 0 := by sorry
