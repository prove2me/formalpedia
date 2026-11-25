-- Prove2me | Theorems.Thm_SimpleGraph_goodman_within
-- name    : SimpleGraph.goodman_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:30:46.978655+00:00
-- url     : https://prove2.me/theorems/c2298e5e-c073-4961-a1e1-27ea581d5051
-- title:
--   Simple Graph: goodman within
-- statement:
--   **Goodman's formula inside a finite set.** For every finite vertex set `S`, twice the number of
--   monochromatic triangles in `S` plus the number of mixed wedges in `S` is `2 * C(|S|, 3)`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L272-L323
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L272-L323

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

theorem SimpleGraph.goodman_within (S : Finset V) :
    2 * (G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3) +
        ∑ v ∈ S, G.degreeWithin S v * Gᶜ.degreeWithin S v = 2 * (#S).choose 3 := by sorry
