-- Prove2me | Theorems.Thm_P010_prime_segments_partition
-- name    : P010.prime_segments_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:56.478179+00:00
-- url     : https://prove2.me/theorems/4756c3fa-bf6e-4b28-ba42-007ed70b34ab
-- title:
--   P010: prime segments partition
-- statement:
--   The three disjoint arithmetic prime ranges partition all
--   primes up to n.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1799-L1815
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1799-L1815

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.prime_segments_partition (n : ℕ) :
    (n / 3).primesLE ∪ middlePrimes n ∪ largePrimes n =
      n.primesLE := by sorry
