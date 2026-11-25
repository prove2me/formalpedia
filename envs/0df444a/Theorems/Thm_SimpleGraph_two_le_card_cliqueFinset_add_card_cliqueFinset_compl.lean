-- Prove2me | Theorems.Thm_SimpleGraph_two_le_card_cliqueFinset_add_card_cliqueFinset_compl
-- name    : SimpleGraph.two_le_card_cliqueFinset_add_card_cliqueFinset_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:41:43.73393+00:00
-- url     : https://prove2.me/theorems/3b92fe50-ada1-575a-aa09-713ec98c2903
-- title:
--   Simple Graph: two le card clique Finset add card clique Finset compl
-- statement:
--   Every red/blue colouring of `K_6` has at least two monochromatic triangles.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L451-L455
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L451-L455

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

theorem SimpleGraph.two_le_card_cliqueFinset_add_card_cliqueFinset_compl (h6 : Fintype.card V = 6) :
    2 ≤ #(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) := by sorry
