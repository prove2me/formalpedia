-- Prove2me | Theorems.Thm_SimpleGraph_sum_cliqueCountIn_neighbors_eq
-- name    : SimpleGraph.sum_cliqueCountIn_neighbors_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:44.540946+00:00
-- url     : https://prove2.me/theorems/61443c7b-1cd8-412a-ab5a-fac5924eb731
-- title:
--   Simple Graph: sum clique Count In neighbors eq
-- statement:
--   **Rooted double count.** For `1 ≤ j`, summing over `v ∈ S` the number of `(j - 1)`-cliques in
--   the neighbourhood of `v` in `S` counts each `j`-clique of `S` once per vertex: the sum is
--   `j` times the number of `j`-cliques in `S`. (At `j = 0` the identity fails under natural
--   subtraction.)
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L203-L242
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L203-L242

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

theorem SimpleGraph.sum_cliqueCountIn_neighbors_eq (S : Finset V) {j : ℕ} (hj : 1 ≤ j) :
    ∑ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1) = j * G.cliqueCountIn S j := by sorry
