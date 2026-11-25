-- Prove2me | Theorems.Thm_SimpleGraph_cliqueCountIn_eq_card_cliqueFinset_induce
-- name    : SimpleGraph.cliqueCountIn_eq_card_cliqueFinset_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:48.181379+00:00
-- url     : https://prove2.me/theorems/052502c3-e96f-4b2f-9197-4841beb8e78f
-- title:
--   Simple Graph: clique Count In eq card clique Finset induce
-- statement:
--   The number of `k`-cliques of `G` inside `S` is the number of `k`-cliques of `G.induce S`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L115-L136
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L115-L136

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

theorem SimpleGraph.cliqueCountIn_eq_card_cliqueFinset_induce (S : Finset V) (k : ℕ) :
    G.cliqueCountIn S k = #((G.induce (S : Set V)).cliqueFinset k) := by sorry
