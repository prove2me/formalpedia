-- Prove2me | Theorems.Thm_SimpleGraph_Walk_induce_support_isTree_of_length_eq_dist
-- name    : SimpleGraph.Walk.induce_support_isTree_of_length_eq_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:54.563254+00:00
-- url     : https://prove2.me/theorems/3b2f1902-e054-4626-911c-6248aa77dcea
-- title:
--   Walk: induce support is Tree of length eq dist
-- statement:
--   A shortest walk induces a tree on its support.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L151-L200
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L151-L200

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

theorem SimpleGraph.Walk.induce_support_isTree_of_length_eq_dist {G : SimpleGraph α} {u v : α}
    (p : G.Walk u v) (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by sorry
