-- Prove2me | Theorems.Thm_SimpleGraph_ContainsBook_not_cliqueFree_or
-- name    : SimpleGraph.ContainsBook.not_cliqueFree_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:46.335465+00:00
-- url     : https://prove2.me/theorems/f711d9ed-8bd2-4d0c-b926-9c6b11ac0b2f
-- title:
--   Contains Book: not clique Free or
-- statement:
--   **Book forcing.** If `G` has a book with an `m`-vertex spine and `n` pages, and
--   `RamseyBound n (r - m) s`, then `G` has an `r`-clique or `Gᶜ` has an `s`-clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L102-L106
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L102-L106

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
public import Theorems.Thm_SimpleGraph_RamseyBound_not_cliqueFree_or

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem SimpleGraph.ContainsBook.not_cliqueFree_or {m n r s : ℕ} (hB : G.ContainsBook m n)
    (h : RamseyBound n (r - m) s) : ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree s := by sorry
