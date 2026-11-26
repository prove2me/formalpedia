-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_sum_obstruction_product_expand
-- name    : Sabidussi.OddBalance.sum_obstruction_product_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:33.191024+00:00
-- url     : https://prove2.me/theorems/63643309-6d66-5f38-abdb-2f43c4b36b1e
-- title:
--   Odd Balance: sum obstruction product expand
-- statement:
--   The Odd Balance construction uses the sum obstruction product expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L101-L106
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L101-L106

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

theorem Sabidussi.OddBalance.sum_obstruction_product_expand
    (b : V → V → Fin 3 → Fin 3 → F2) (S : Finset V) :
    (∑ x : V → Fin 3, ∏ v ∈ S, obstruction b x v) =
      ∑ f : Choice S, totalChoiceTerm b S f := by sorry
