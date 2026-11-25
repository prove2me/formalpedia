-- Prove2me | Theorems.Thm_SimpleGraph_containsBook_two_iff
-- name    : SimpleGraph.containsBook_two_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:39.278947+00:00
-- url     : https://prove2.me/theorems/31b4885b-72f7-5f60-9e2e-cce1db87c936
-- title:
--   Simple Graph: contains Book two iff
-- statement:
--   A book with a two-vertex spine is an edge with at least `t` common neighbours.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L119-L147
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L119-L147

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

theorem SimpleGraph.containsBook_two_iff {t : ℕ} :
    G.ContainsBook 2 t ↔ ∃ u v, G.Adj u v ∧ t ≤ Fintype.card (G.commonNeighbors u v) := by sorry
