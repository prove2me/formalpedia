-- Prove2me | Theorems.Thm_SimpleGraph_Coloring_ofMycielski_ne_apex
-- name    : SimpleGraph.Coloring.ofMycielski_ne_apex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:00:23.365978+00:00
-- url     : https://prove2.me/theorems/d1c4dd5b-aff5-5636-8763-4a2df3b889a9
-- title:
--   Coloring: of Mycielski ne apex
-- statement:
--   The recolored original graph omits the apex color.
--
--   Source: https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L101-L108
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L101-L108

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

theorem SimpleGraph.Coloring.ofMycielski_ne_apex (C : G.mycielski.Coloring α) (v : V) :
    C.ofMycielski v ≠ C none := by sorry
