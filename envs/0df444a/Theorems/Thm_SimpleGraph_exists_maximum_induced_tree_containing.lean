-- Prove2me | Theorems.Thm_SimpleGraph_exists_maximum_induced_tree_containing
-- name    : SimpleGraph.exists_maximum_induced_tree_containing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:54.261578+00:00
-- url     : https://prove2.me/theorems/e14bd6eb-9206-4461-b141-0eaae9d008eb
-- title:
--   Simple Graph: exists maximum induced tree containing
-- statement:
--   A nonempty family of induced trees with prescribed vertices has a largest member.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L271-L288
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L271-L288

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
public import Definitions.Def_Wowii84_LargestInducedTree
set_option autoImplicit false
@[expose] public section
public section
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α]

theorem SimpleGraph.exists_maximum_induced_tree_containing (G : SimpleGraph α) (r : Finset α)
    (hr : ∃ s : Finset α, r ⊆ s ∧ (G.induce (s : Set α)).IsTree) :
    ∃ s : Finset α,
      r ⊆ s ∧
      (G.induce (s : Set α)).IsTree ∧
      ∀ t : Finset α, r ⊆ t →
        (G.induce (t : Set α)).IsTree → t.card ≤ s.card := by sorry
