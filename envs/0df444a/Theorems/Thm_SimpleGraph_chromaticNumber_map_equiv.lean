-- Prove2me | Theorems.Thm_SimpleGraph_chromaticNumber_map_equiv
-- name    : SimpleGraph.chromaticNumber_map_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:00:44.520595+00:00
-- url     : https://prove2.me/theorems/69e4c71e-7318-5c6a-85e3-f87d7860e18a
-- title:
--   Simple Graph: chromatic Number map equiv
-- statement:
--   Relabelling vertices preserves the chromatic number.
--
--   Source: https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L169-L173
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L169-L173

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

theorem SimpleGraph.chromaticNumber_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e).chromaticNumber = G.chromaticNumber := by sorry
