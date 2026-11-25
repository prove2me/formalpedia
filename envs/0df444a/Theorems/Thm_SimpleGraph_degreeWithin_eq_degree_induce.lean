-- Prove2me | Theorems.Thm_SimpleGraph_degreeWithin_eq_degree_induce
-- name    : SimpleGraph.degreeWithin_eq_degree_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:29.136714+00:00
-- url     : https://prove2.me/theorems/f91fcdbb-9d03-5e04-9c57-dd62bc954407
-- title:
--   Simple Graph: degree Within eq degree induce
-- statement:
--   The degree within `S` of a vertex of `S` is its degree in the induced graph `G.induce S`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L105-L112
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L105-L112

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
omit [DecidableEq V]

theorem SimpleGraph.degreeWithin_eq_degree_induce {S : Finset V} {v : V} (hv : v ∈ S) :
    G.degreeWithin S v = (G.induce (S : Set V)).degree ⟨v, hv⟩ := by sorry
