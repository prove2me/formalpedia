-- Prove2me | Theorems.Thm_P010_noncoprime_cover_lower_counts
-- name    : P010.noncoprime_cover_lower_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:05.106667+00:00
-- url     : https://prove2.me/theorems/f926387b-f132-45ff-8f63-57a8c3b96e56
-- title:
--   P010: noncoprime cover lower counts
-- statement:
--   The global path-cover lower bounds from isolated vertices,
--   degree-one middle primes and the remaining vertex 2.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L765-L821
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L765-L821

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.noncoprime_cover_lower_counts (n : ℕ) (hn : 4 ≤ n)
    (paths : List (List ℕ))
    (hcover : IsPermutation n paths.flatten)
    (hchains : ∀ p ∈ paths, NonCoprimeChain p) :
    2 * (isolatedVertices n).card + (middlePrimes n).card ≤
        2 * paths.length ∧
      (isolatedVertices n).card + 1 ≤ paths.length := by sorry
