-- Prove2me | Theorems.Thm_SimpleGraph_sum_card_commonNeighbors_eq
-- name    : SimpleGraph.sum_card_commonNeighbors_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:52.968993+00:00
-- url     : https://prove2.me/theorems/24d2e323-16b4-5c14-91df-bdda999c5f2c
-- title:
--   Simple Graph: sum card common Neighbors eq
-- statement:
--   **Codegrees count triangles.** Summing the codegree over ordered adjacent pairs counts each
--   triangle six times.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L214-L217
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L214-L217

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

theorem SimpleGraph.sum_card_commonNeighbors_eq [DecidableEq V] :
    ∑ u, ∑ v ∈ G.neighborFinset u, Fintype.card (G.commonNeighbors u v) =
      6 * #(G.cliqueFinset 3) := by sorry
