-- Prove2me | Theorems.Thm_SimpleGraph_goodman_bound
-- name    : SimpleGraph.goodman_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:31:10.492657+00:00
-- url     : https://prove2.me/theorems/a33ee8ef-926e-4b14-8703-0fd6af850c0e
-- title:
--   Simple Graph: goodman bound
-- statement:
--   **Goodman's bound.** Every red/blue colouring of `K_n` has at least `n (n - 1) (n - 5) / 24`
--   monochromatic triangles.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L406-L409
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L406-L409

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
variable [Fintype V]

theorem SimpleGraph.goodman_bound :
    Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 5) ≤
      24 * (#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3)) := by sorry
