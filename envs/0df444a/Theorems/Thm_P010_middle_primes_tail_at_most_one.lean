-- Prove2me | Theorems.Thm_P010_middle_primes_tail_at_most_one
-- name    : P010.middle_primes_tail_at_most_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:36:44.442553+00:00
-- url     : https://prove2.me/theorems/9c2c96ea-e067-44d5-9dda-2531112de2c7
-- title:
--   P010: middle primes tail at most one
-- statement:
--   In a simple non-coprime path with at least two vertices, at most one
--   middle-range prime can occur after its first vertex.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L418-L462
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L418-L462

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.middle_primes_tail_at_most_one (n x y : ℕ) (xs : List ℕ)
    (hchain : NonCoprimeChain (x :: y :: xs))
    (hnodup : (x :: y :: xs).Nodup)
    (hbound : ∀ t ∈ x :: y :: xs, 0 < t ∧ t ≤ n) :
    ((y :: xs).filter (fun t => decide (t ∈ middlePrimes n))).length ≤ 1 := by sorry
