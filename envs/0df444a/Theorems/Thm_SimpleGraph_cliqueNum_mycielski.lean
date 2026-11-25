-- Prove2me | Theorems.Thm_SimpleGraph_cliqueNum_mycielski
-- name    : SimpleGraph.cliqueNum_mycielski
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:00:38.088839+00:00
-- url     : https://prove2.me/theorems/9ef27ac6-0901-51f0-a3f4-69e950570b52
-- title:
--   Simple Graph: clique Num mycielski
-- statement:
--   The Mycielski graph of a nonempty triangle-free finite graph has clique number two.
--
--   Source: https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L146-L154
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L146-L154

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

theorem SimpleGraph.cliqueNum_mycielski [Finite V] [Nonempty V] {G : SimpleGraph V}
    (hG : G.CliqueFree 3) : G.mycielski.cliqueNum = 2 := by sorry
