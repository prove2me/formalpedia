-- Prove2me | Theorems.Thm_SimpleGraph_Connected_exists_induced_tree_containing_pair
-- name    : SimpleGraph.Connected.exists_induced_tree_containing_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:51.553958+00:00
-- url     : https://prove2.me/theorems/19662c9b-b03c-454b-9fa0-87d366ee53d3
-- title:
--   Connected: exists induced tree containing pair
-- statement:
--   Every pair of vertices in a connected graph lies in an induced tree.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L260-L267
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L260-L267

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
omit [Fintype α]

theorem SimpleGraph.Connected.exists_induced_tree_containing_pair {G : SimpleGraph α}
    (hG : G.Connected) (x y : α) :
    ∃ s : Finset α, x ∈ s ∧ y ∈ s ∧ (G.induce (s : Set α)).IsTree := by sorry
