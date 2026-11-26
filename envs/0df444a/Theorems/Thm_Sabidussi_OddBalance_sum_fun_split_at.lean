-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_sum_fun_split_at
-- name    : Sabidussi.OddBalance.sum_fun_split_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:47.582577+00:00
-- url     : https://prove2.me/theorems/b453f59a-4782-5d75-b8de-11ed7748fcd6
-- title:
--   Odd Balance: sum fun split at
-- statement:
--   The Odd Balance construction uses the sum fun split at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L108-L120
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L108-L120

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

theorem Sabidussi.OddBalance.sum_fun_split_at {A M : Type*} [Fintype A] [AddCommMonoid M]
    (w : V) (F : (V → A) → M) :
    (∑ x : V → A, F x) =
      ∑ a : A, ∑ y : ({v : V // v ≠ w} → A),
        F ((Equiv.funSplitAt w A).symm (a, y)) := by sorry
