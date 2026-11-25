-- Prove2me | Theorems.Thm_SimpleGraph_CliqueFree_cliqueNum_le_two
-- name    : SimpleGraph.CliqueFree.cliqueNum_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:00:11.376095+00:00
-- url     : https://prove2.me/theorems/96af663b-b5d9-4133-9ef9-f56ecd2bced7
-- title:
--   Clique Free: clique Num le two
-- statement:
--   A triangle-free graph has clique number at most two.
--
--   Source: https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L139-L143
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L139-L143

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

theorem SimpleGraph.CliqueFree.cliqueNum_le_two {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    G.cliqueNum ≤ 2 := by sorry
