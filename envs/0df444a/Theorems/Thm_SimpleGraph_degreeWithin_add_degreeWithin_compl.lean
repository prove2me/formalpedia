-- Prove2me | Theorems.Thm_SimpleGraph_degreeWithin_add_degreeWithin_compl
-- name    : SimpleGraph.degreeWithin_add_degreeWithin_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:31:10.374107+00:00
-- url     : https://prove2.me/theorems/34aa614f-56c3-5eb7-b936-681f25550623
-- title:
--   Simple Graph: degree Within add degree Within compl
-- statement:
--   Inside `S`, a vertex of `S` has `#S - 1` neighbours in `G` and `Gᶜ` together.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L139-L152
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L139-L152

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

theorem SimpleGraph.degreeWithin_add_degreeWithin_compl {S : Finset V} {v : V} (hv : v ∈ S) :
    G.degreeWithin S v + Gᶜ.degreeWithin S v + 1 = #S := by sorry
