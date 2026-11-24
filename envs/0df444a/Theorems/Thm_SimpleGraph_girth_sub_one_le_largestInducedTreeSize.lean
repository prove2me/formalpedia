-- Prove2me | Theorems.Thm_SimpleGraph_girth_sub_one_le_largestInducedTreeSize
-- name    : SimpleGraph.girth_sub_one_le_largestInducedTreeSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:32:01.465839+00:00
-- url     : https://prove2.me/theorems/cf877148-1812-43fe-be1f-203c9acbd7f9
-- title:
--   Simple Graph: girth sub one le largest Induced Tree Size
-- statement:
--   Removing one vertex from a shortest cycle gives an induced tree.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L203-L256
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L203-L256

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

theorem SimpleGraph.girth_sub_one_le_largestInducedTreeSize (G : SimpleGraph α)
    (hcyc : ¬ G.IsAcyclic) :
    G.girth - 1 ≤ largestInducedTreeSize G := by sorry
