-- Prove2me | Theorems.Thm_SimpleGraph_exists_adj_card_commonNeighbors_pos
-- name    : SimpleGraph.exists_adj_card_commonNeighbors_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:32:45.288024+00:00
-- url     : https://prove2.me/theorems/d5c08e46-33b8-5e66-994c-0de029ce8d7c
-- title:
--   Simple Graph: exists adj card common Neighbors pos
-- statement:
--   **Mantel's theorem, book form.** A graph on `n` vertices with more than `n² / 4` edges has an
--   edge whose endpoints have a common neighbour.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L306-L312
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L306-L312

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

theorem SimpleGraph.exists_adj_card_commonNeighbors_pos (h : Fintype.card V ^ 2 < 4 * #G.edgeFinset) :
    ∃ u v, G.Adj u v ∧ 0 < Fintype.card (G.commonNeighbors u v) := by sorry
