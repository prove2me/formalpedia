-- Prove2me | Theorems.Thm_SimpleGraph_card_commonNeighbors_eq_card_filter
-- name    : SimpleGraph.card_commonNeighbors_eq_card_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:11.740798+00:00
-- url     : https://prove2.me/theorems/a7a87dc6-55c0-4036-87da-9bb5f87758f8
-- title:
--   Simple Graph: card common Neighbors eq card filter
-- statement:
--   The codegree as the size of a filtered `Finset`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L111-L116
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L111-L116

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

theorem SimpleGraph.card_commonNeighbors_eq_card_filter (u v : V) :
    Fintype.card (G.commonNeighbors u v) = #{w | G.Adj u w ∧ G.Adj v w} := by sorry
