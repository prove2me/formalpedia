-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_prod_sum_expand
-- name    : Sabidussi.OddBalance.prod_sum_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:12:40.083797+00:00
-- url     : https://prove2.me/theorems/7252bade-3b3f-57a9-b973-cff22b9f025c
-- title:
--   Odd Balance: prod sum expand
-- statement:
--   The Odd Balance construction uses the prod sum expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L67-L74
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L67-L74

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

theorem Sabidussi.OddBalance.prod_sum_expand (S : Finset V) (t : V → Finset V) (a : V → V → F2) :
    (∏ v ∈ S, ∑ u ∈ t v, a v u) =
      ∑ f : (v : {v // v ∈ S}) → {u // u ∈ t v},
        ∏ v : {v // v ∈ S}, a v (f v) := by sorry
