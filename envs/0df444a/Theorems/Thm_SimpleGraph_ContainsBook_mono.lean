-- Prove2me | Theorems.Thm_SimpleGraph_ContainsBook_mono
-- name    : SimpleGraph.ContainsBook.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:43.461479+00:00
-- url     : https://prove2.me/theorems/e9f51c30-c57e-4316-98c1-e49746aa4d70
-- title:
--   Contains Book: mono
-- statement:
--   Fewer pages: a book with `t` pages has `t' ≤ t` pages.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L70-L73
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L70-L73

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
public import Theorems.Thm_SimpleGraph_RamseyBound_mono

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem SimpleGraph.ContainsBook.mono {m t t' : ℕ} (h : G.ContainsBook m t) (ht : t' ≤ t) :
    G.ContainsBook m t' := by sorry
