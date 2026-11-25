-- Prove2me | Theorems.Thm_SimpleGraph_goodman_sq_within
-- name    : SimpleGraph.goodman_sq_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:30:51.000778+00:00
-- url     : https://prove2.me/theorems/54f1406a-1dfb-4aae-9346-65af8625f5f1
-- title:
--   Simple Graph: goodman sq within
-- statement:
--   **Goodman's formula with degree imbalance, inside a finite set.**
--   `8 (T + T') + |S| (|S| - 1) ^ 2 = 8 C(|S|, 3) + ∑ v ∈ S, (d v - d' v) ^ 2`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L345-L362
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L345-L362

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem SimpleGraph.goodman_sq_within (S : Finset V) :
    8 * ((G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3 : ℕ) : ℤ) + #S * ((#S : ℤ) - 1) ^ 2 =
      8 * (#S).choose 3 + ∑ v ∈ S, ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 := by sorry
