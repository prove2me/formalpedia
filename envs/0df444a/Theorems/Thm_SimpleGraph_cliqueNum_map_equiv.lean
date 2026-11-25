-- Prove2me | Theorems.Thm_SimpleGraph_cliqueNum_map_equiv
-- name    : SimpleGraph.cliqueNum_map_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:00:41.696797+00:00
-- url     : https://prove2.me/theorems/15751318-d6cc-54d4-920b-8d2fbd570d78
-- title:
--   Simple Graph: clique Num map equiv
-- statement:
--   Relabelling vertices preserves the clique number.
--
--   Source: https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L159-L166
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L159-L166

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
public import Definitions.Def_Erdos627_Mycielski
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
variable {V : Type*}
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
variable {W : Type*}

theorem SimpleGraph.cliqueNum_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e).cliqueNum = G.cliqueNum := by sorry
