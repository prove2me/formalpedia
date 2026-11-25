-- Prove2me | Theorems.Thm_SimpleGraph_goodman_bound_of_even_card
-- name    : SimpleGraph.goodman_bound_of_even_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:41:35.537227+00:00
-- url     : https://prove2.me/theorems/b42862a8-a15b-5708-bbd7-1a108d2b5975
-- title:
--   Simple Graph: goodman bound of even card
-- statement:
--   **Goodman's bound for even orders.** If `n` is even, every red/blue colouring of `K_n` has at
--   least `n (n - 2) (n - 4) / 24` monochromatic triangles: each red and blue degree differ by an odd
--   number, so every squared difference in `goodman_sq` is at least `1`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L414-L431
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L414-L431

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

theorem SimpleGraph.goodman_bound_of_even_card (hn : Even (Fintype.card V)) :
    (Fintype.card V : ℤ) * (Fintype.card V - 2) * (Fintype.card V - 4) ≤
      24 * ((#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) : ℕ) : ℤ) := by sorry
