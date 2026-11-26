-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_sum_derangement_totalChoiceTerm_eq_zero
-- name    : Sabidussi.OddBalance.sum_derangement_totalChoiceTerm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:55.20264+00:00
-- url     : https://prove2.me/theorems/d861b173-d3a1-5f79-8a81-c3e630e11b7f
-- title:
--   Odd Balance: sum derangement total Choice Term eq zero
-- statement:
--   The Odd Balance construction uses the sum derangement total Choice Term eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L408-L427
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L408-L427

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

theorem Sabidussi.OddBalance.sum_derangement_totalChoiceTerm_eq_zero
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ d : Derangement S, totalChoiceTerm b S d.choice) = 0 := by sorry
