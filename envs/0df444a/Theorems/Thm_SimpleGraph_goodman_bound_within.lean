-- Prove2me | Theorems.Thm_SimpleGraph_goodman_bound_within
-- name    : SimpleGraph.goodman_bound_within
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:31:12.925442+00:00
-- url     : https://prove2.me/theorems/68bd25f8-a936-5cba-a6b8-b92834afdb16
-- title:
--   Simple Graph: goodman bound within
-- statement:
--   **Goodman's bound inside a finite set.** Every finite vertex set `S` contains at least
--   `|S| (|S| - 1) (|S| - 5) / 24` monochromatic triangles.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L366-L377
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L366-L377

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

theorem SimpleGraph.goodman_bound_within (S : Finset V) :
    #S * (#S - 1) * (#S - 5) ≤ 24 * (G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3) := by sorry
