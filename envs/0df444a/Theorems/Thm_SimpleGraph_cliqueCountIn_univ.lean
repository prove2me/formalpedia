-- Prove2me | Theorems.Thm_SimpleGraph_cliqueCountIn_univ
-- name    : SimpleGraph.cliqueCountIn_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:30:45.02788+00:00
-- url     : https://prove2.me/theorems/59f4faf4-76bc-493d-a393-46cd2e58059e
-- title:
--   Simple Graph: clique Count In univ
-- statement:
--   The number of `k`-cliques inside `univ` is the number of `k`-cliques.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L96-L101
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L96-L101

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

theorem SimpleGraph.cliqueCountIn_univ [Fintype V] (k : ℕ) :
    G.cliqueCountIn univ k = #(G.cliqueFinset k) := by sorry
