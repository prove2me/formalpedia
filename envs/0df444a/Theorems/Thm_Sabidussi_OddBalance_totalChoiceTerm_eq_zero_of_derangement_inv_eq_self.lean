-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_eq_zero_of_derangement_inv_eq_self
-- name    : Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_derangement_inv_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:54.794028+00:00
-- url     : https://prove2.me/theorems/6fc463e9-76e1-57e2-b64c-9f8cd3ec8747
-- title:
--   Odd Balance: total Choice Term eq zero of derangement inv eq self
-- statement:
--   The Odd Balance construction uses the total Choice Term eq zero of derangement inv eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L314-L340
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L314-L340

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

theorem Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_derangement_inv_eq_self
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) (d : Derangement S) (hd : d.inv = d) :
    totalChoiceTerm b S d.choice = 0 := by sorry
