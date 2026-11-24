-- Prove2me | Theorems.Thm_SimpleGraph_girth_add_one_le_largestInducedTreeSize_of_two_leaves
-- name    : SimpleGraph.girth_add_one_le_largestInducedTreeSize_of_two_leaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:32:10.110489+00:00
-- url     : https://prove2.me/theorems/5f0db7b5-b21c-41ef-8527-6e545e1a14c6
-- title:
--   Simple Graph: girth add one le largest Induced Tree Size of two leaves
-- statement:
--   Two distinct leaves in a connected cyclic graph yield an induced tree of order at least girth plus one.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L416-L454
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L416-L454

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

theorem SimpleGraph.girth_add_one_le_largestInducedTreeSize_of_two_leaves
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hcyc : ¬ G.IsAcyclic)
    {x y : α} (hxy : x ≠ y)
    (hx : G.degree x = 1) (hy : G.degree y = 1) :
    G.girth + 1 ≤ largestInducedTreeSize G := by sorry
