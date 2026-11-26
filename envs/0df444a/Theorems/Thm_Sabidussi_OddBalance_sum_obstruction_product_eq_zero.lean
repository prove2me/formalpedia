-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_sum_obstruction_product_eq_zero
-- name    : Sabidussi.OddBalance.sum_obstruction_product_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:03.083797+00:00
-- url     : https://prove2.me/theorems/c7b87c94-acb7-504d-baeb-b047ba4dac09
-- title:
--   Odd Balance: sum obstruction product eq zero
-- statement:
--   The Odd Balance construction uses the sum obstruction product eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L480-L487
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L480-L487

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

theorem Sabidussi.OddBalance.sum_obstruction_product_eq_zero
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ x : V → Fin 3, ∏ v ∈ S, obstruction b x v) = 0 := by sorry
