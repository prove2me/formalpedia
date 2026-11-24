-- Prove2me | Theorems.Thm_SimpleGraph_IsTree_induce_insert_of_unique_adj
-- name    : SimpleGraph.IsTree.induce_insert_of_unique_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:50.538524+00:00
-- url     : https://prove2.me/theorems/7b32cb6f-406b-4c26-87db-ee959919b146
-- title:
--   Is Tree: induce insert of unique adj
-- statement:
--   Attaching a new vertex along its unique neighbor in an induced tree gives a larger
--   induced tree.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L81-L146
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L81-L146

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

theorem SimpleGraph.IsTree.induce_insert_of_unique_adj {G : SimpleGraph α} {s : Finset α} {z a : α}
    (hT : (G.induce (s : Set α)).IsTree)
    (_hz : z ∉ s) (ha : a ∈ s) (hza : G.Adj z a)
    (huniq : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = a) :
    (G.induce ((insert z s : Finset α) : Set α)).IsTree := by sorry
