-- Prove2me | Theorems.Thm_SimpleGraph_Connected_exists_adj_finset_compl
-- name    : SimpleGraph.Connected.exists_adj_finset_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:55.925906+00:00
-- url     : https://prove2.me/theorems/f69e5271-4bd9-44e5-a2e5-6f5bdf5feb46
-- title:
--   Connected: exists adj finset compl
-- statement:
--   A nonempty proper vertex set in a connected graph has an edge across its boundary.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L291-L304
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean#L291-L304

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

theorem SimpleGraph.Connected.exists_adj_finset_compl {G : SimpleGraph α}
    (hG : G.Connected) {s : Finset α} (hs : s.Nonempty) (hsu : s ≠ Finset.univ) :
    ∃ z ∉ s, ∃ a ∈ s, G.Adj z a := by sorry
