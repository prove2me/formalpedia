-- Prove2me | Theorems.Thm_SimpleGraph_ContainsBook_mono_spine
-- name    : SimpleGraph.ContainsBook.mono_spine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:32:33.533193+00:00
-- url     : https://prove2.me/theorems/05c409ec-86aa-4cee-84d8-afa5ae45118a
-- title:
--   Contains Book: mono spine
-- statement:
--   A shorter spine: a book with an `m`-vertex spine has an `m'`-vertex spine for `m' ≤ m`, with
--   the same pages.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L77-L82
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L77-L82

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

theorem SimpleGraph.ContainsBook.mono_spine {m m' t : ℕ} (h : G.ContainsBook m t) (hm : m' ≤ m) :
    G.ContainsBook m' t := by sorry
