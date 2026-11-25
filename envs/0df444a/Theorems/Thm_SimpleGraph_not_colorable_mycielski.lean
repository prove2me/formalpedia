-- Prove2me | Theorems.Thm_SimpleGraph_not_colorable_mycielski
-- name    : SimpleGraph.not_colorable_mycielski
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:00:41.073239+00:00
-- url     : https://prove2.me/theorems/ad53e196-6b1b-431e-83cb-c15fb239de41
-- title:
--   Simple Graph: not colorable mycielski
-- statement:
--   A Mycielski graph is not `k`-colorable if the original graph has chromatic number at least `k`.
--
--   Source: https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L111-L116
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L111-L116

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

theorem SimpleGraph.not_colorable_mycielski (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    ¬G.mycielski.Colorable k := by sorry
