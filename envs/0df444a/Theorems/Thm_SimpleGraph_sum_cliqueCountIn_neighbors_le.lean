-- Prove2me | Theorems.Thm_SimpleGraph_sum_cliqueCountIn_neighbors_le
-- name    : SimpleGraph.sum_cliqueCountIn_neighbors_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:42:41.761183+00:00
-- url     : https://prove2.me/theorems/0598615f-de22-4edf-9177-b240d8095f8f
-- title:
--   Simple Graph: sum clique Count In neighbors le
-- statement:
--   **Rooted double count**, inequality form of `sum_cliqueCountIn_neighbors_eq`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L245-L247
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L245-L247

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem SimpleGraph.sum_cliqueCountIn_neighbors_le (S : Finset V) {j : ℕ} (hj : 1 ≤ j) :
    ∑ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1) ≤ j * G.cliqueCountIn S j := by sorry
