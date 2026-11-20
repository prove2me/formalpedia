-- Prove2me | Theorems.Thm_P010_intermediateUnits_perm
-- name    : P010.intermediateUnits_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:47.044624+00:00
-- url     : https://prove2.me/theorems/87d94565-419a-4077-be30-2e35ef09e4f7
-- title:
--   P010: intermediate Units perm
-- statement:
--   Pair-unit concatenation is a permutation of the catalogs for
--   all primes occurring in the pairs, in pair order.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1951-L1971
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1951-L1971

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.intermediateUnits_perm (n : ℕ) (pairs : List (ℕ × ℕ))
    (hn : 12 ≤ n)
    (hpairs : ∀ pair ∈ pairs,
      pair.1 ∈ intermediatePrimes n ∧
        pair.2 ∈ intermediatePrimes n) :
    (pairs.map (intermediateEvenUnit n)).flatten.Perm
      (classConcat n (pairs.flatMap (fun pq => [pq.1, pq.2]))) := by sorry
