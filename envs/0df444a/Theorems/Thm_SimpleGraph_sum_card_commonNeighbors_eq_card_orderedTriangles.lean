-- Prove2me | Theorems.Thm_SimpleGraph_sum_card_commonNeighbors_eq_card_orderedTriangles
-- name    : SimpleGraph.sum_card_commonNeighbors_eq_card_orderedTriangles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:40.562315+00:00
-- url     : https://prove2.me/theorems/9ed702a9-3fd9-5593-92c1-a69d51ee4aa2
-- title:
--   Simple Graph: sum card common Neighbors eq card ordered Triangles
-- statement:
--   Summing codegrees over ordered adjacent pairs counts ordered triangles.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L156-L164
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L156-L164

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]

theorem SimpleGraph.sum_card_commonNeighbors_eq_card_orderedTriangles :
    ∑ u, ∑ v ∈ G.neighborFinset u, Fintype.card (G.commonNeighbors u v) =
      #G.orderedTriangles := by sorry
