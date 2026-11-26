-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_sum_prod_one_add_expand
-- name    : Sabidussi.OddBalance.sum_prod_one_add_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:28.881613+00:00
-- url     : https://prove2.me/theorems/b75580b0-05b0-5805-a5fd-a5e546a9ed16
-- title:
--   Odd Balance: sum prod one add expand
-- statement:
--   The Odd Balance construction uses the sum prod one add expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L61-L65
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L61-L65

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

theorem Sabidussi.OddBalance.sum_prod_one_add_expand (q : (V → Fin 3) → V → F2) :
    (∑ x : V → Fin 3, ∏ v : V, (1 + q x v)) =
      ∑ S ∈ Finset.univ.powerset, ∑ x : V → Fin 3, ∏ v ∈ S, q x v := by sorry
