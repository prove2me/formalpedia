-- Prove2me | Theorems.Thm_SimpleGraph_ContainsBook_mono_graph
-- name    : SimpleGraph.ContainsBook.mono_graph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:32:25.457215+00:00
-- url     : https://prove2.me/theorems/40107b8d-ec8a-46b2-bdad-72a6e6115315
-- title:
--   Contains Book: mono graph
-- statement:
--   A book of `G` is a book of every supergraph of `G`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L85-L89
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L85-L89

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

theorem SimpleGraph.ContainsBook.mono_graph {H : SimpleGraph V} {m t : ℕ} (h : G.ContainsBook m t)
    (hGH : G ≤ H) : H.ContainsBook m t := by sorry
