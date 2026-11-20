-- Prove2me | Theorems.Thm_P010_large_prime_path_singleton
-- name    : P010.large_prime_path_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:37:06.812035+00:00
-- url     : https://prove2.me/theorems/2b2cfa50-57cd-4b96-b1d0-11bba16c5b87
-- title:
--   P010: large prime path singleton
-- statement:
--   Every large prime is a singleton in any simple non-coprime path
--   containing it and lying within [1,n].
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L541-L552
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L541-L552

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.large_prime_path_singleton (n p : ℕ) (a : List ℕ)
    (hp : p ∈ largePrimes n)
    (hchain : NonCoprimeChain a)
    (hnodup : a.Nodup)
    (hmem : p ∈ a)
    (hbound : ∀ t ∈ a, 0 < t ∧ t ≤ n) :
    a = [p] := by sorry
