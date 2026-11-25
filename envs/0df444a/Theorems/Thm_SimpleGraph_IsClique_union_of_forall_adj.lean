-- Prove2me | Theorems.Thm_SimpleGraph_IsClique_union_of_forall_adj
-- name    : SimpleGraph.IsClique.union_of_forall_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:56.02134+00:00
-- url     : https://prove2.me/theorems/00937bf2-4c27-426f-9400-d94be9a62e5d
-- title:
--   Is Clique: union of forall adj
-- statement:
--   A clique glued to a set of common neighbours is a clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L74-L77
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L74-L77

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}

theorem SimpleGraph.IsClique.union_of_forall_adj {s t : Set V} (hs : G.IsClique s)
    (ht : G.IsClique t) (h : ∀ x ∈ s, ∀ y ∈ t, G.Adj x y) : G.IsClique (s ∪ t) := by sorry
