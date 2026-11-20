-- Prove2me | Theorems.Thm_P010_exact_of_matching_bounds
-- name    : P010.exact_of_matching_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:43:07.368173+00:00
-- url     : https://prove2.me/theorems/fbb854cb-f927-4d58-b66f-3ae6b2f9f044
-- title:
--   P010: exact of matching bounds
-- statement:
--   A general extremal principle. This does not supply either arithmetic bound.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L40-L47
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L40-L47

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.exact_of_matching_bounds (n : ℕ)
    (hlower : ∀ a : List ℕ, IsPermutation n a → target n ≤ adjacentCount a)
    (hupper : ∃ a : List ℕ, IsPermutation n a ∧ adjacentCount a ≤ target n) :
    h n = target n := by sorry
