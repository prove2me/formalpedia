-- Prove2me | Theorems.Thm_P010_small_prime_even_endpoints
-- name    : P010.small_prime_even_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:33:50.782194+00:00
-- url     : https://prove2.me/theorems/a5c3c81a-e2f1-4e72-a801-52976a522d9b
-- title:
--   P010: small prime even endpoints
-- statement:
--   The p-class with p ≤ n/4 has two distinct even vertices.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L966-L975
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L966-L975

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.small_prime_even_endpoints (n p : ℕ) (hp : Nat.Prime p)
    (hsmall : 4 * p ≤ n) :
    2 * p ∈ primeClass n p ∧
      4 * p ∈ primeClass n p ∧ 2 * p ≠ 4 * p := by sorry
