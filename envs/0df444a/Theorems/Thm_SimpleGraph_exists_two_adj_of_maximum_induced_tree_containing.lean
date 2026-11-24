-- Prove2me | Theorems.Thm_SimpleGraph_exists_two_adj_of_maximum_induced_tree_containing
-- name    : SimpleGraph.exists_two_adj_of_maximum_induced_tree_containing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:22:52.360485+00:00
-- url     : https://prove2.me/theorems/5d0f928f-6c42-42ef-bcd5-b43946bc9948
-- title:
--   Simple Graph: exists two adj of maximum induced tree containing
-- statement:
--   A boundary vertex of a largest prescribed induced tree has two neighbors in the tree.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L307-L330
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L307-L330

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

theorem SimpleGraph.exists_two_adj_of_maximum_induced_tree_containing
    {G : SimpleGraph α} {r s : Finset α}
    (hG : G.Connected) (hrs : r ⊆ s) (hs : s.Nonempty)
    (hT : (G.induce (s : Set α)).IsTree)
    (hmax : ∀ t : Finset α, r ⊆ t →
      (G.induce (t : Set α)).IsTree → t.card ≤ s.card)
    (hsu : s ≠ Finset.univ) :
    ∃ z ∉ s, ∃ a ∈ s, ∃ b ∈ s,
      a ≠ b ∧ G.Adj z a ∧ G.Adj z b := by sorry
