-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_obstruction_product_expand
-- name    : Sabidussi.OddBalance.obstruction_product_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:34.382822+00:00
-- url     : https://prove2.me/theorems/4ab3fdb4-bccd-4548-b0cb-04b058c31402
-- title:
--   Odd Balance: obstruction product expand
-- statement:
--   The Odd Balance construction uses the obstruction product expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L83-L95
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L83-L95

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

theorem Sabidussi.OddBalance.obstruction_product_expand
    (b : V → V → Fin 3 → Fin 3 → F2) (S : Finset V) (x : V → Fin 3) :
    (∏ v ∈ S, obstruction b x v) =
      ∑ f : Choice S, choiceTerm b S f x := by sorry
