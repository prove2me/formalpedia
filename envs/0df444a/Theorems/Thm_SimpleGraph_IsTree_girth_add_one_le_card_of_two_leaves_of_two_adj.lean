-- Prove2me | Theorems.Thm_SimpleGraph_IsTree_girth_add_one_le_card_of_two_leaves_of_two_adj
-- name    : SimpleGraph.IsTree.girth_add_one_le_card_of_two_leaves_of_two_adj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:22:53.469787+00:00
-- url     : https://prove2.me/theorems/23e26ea2-282d-47df-a7e5-775510892f9e
-- title:
--   Is Tree: girth add one le card of two leaves of two adj
-- statement:
--   Two leaves outside the boundary cycle force an extra two vertices in the induced tree.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L333-L413
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L333-L413

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

theorem SimpleGraph.IsTree.girth_add_one_le_card_of_two_leaves_of_two_adj
    {G : SimpleGraph α} [DecidableRel G.Adj] {s : Finset α}
    (hT : (G.induce (s : Set α)).IsTree)
    {x y z a b : α}
    (hxs : x ∈ s) (hys : y ∈ s) (hxy : x ≠ y)
    (hx : G.degree x = 1) (hy : G.degree y = 1)
    (hz : z ∉ s) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hza : G.Adj z a) (hzb : G.Adj z b) :
    G.girth + 1 ≤ s.card := by sorry
