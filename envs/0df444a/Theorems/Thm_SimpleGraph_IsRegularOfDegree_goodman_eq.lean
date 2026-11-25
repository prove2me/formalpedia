-- Prove2me | Theorems.Thm_SimpleGraph_IsRegularOfDegree_goodman_eq
-- name    : SimpleGraph.IsRegularOfDegree.goodman_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:41:38.176865+00:00
-- url     : https://prove2.me/theorems/3991ddec-5ba7-5bcb-bf19-72cc9992e961
-- title:
--   Is Regular Of Degree: goodman eq
-- statement:
--   **Sharpness of Goodman's bound.** If `G` is regular of degree `k` on `2k + 1` vertices, then
--   `24 (T(G) + T(Gᶜ)) = n (n - 1) (n - 5)` exactly.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L435-L448
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L435-L448

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

theorem SimpleGraph.IsRegularOfDegree.goodman_eq {k : ℕ} (hG : G.IsRegularOfDegree k)
    (hn : Fintype.card V = 2 * k + 1) :
    (24 * (#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3)) : ℤ) =
      Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 5) := by sorry
