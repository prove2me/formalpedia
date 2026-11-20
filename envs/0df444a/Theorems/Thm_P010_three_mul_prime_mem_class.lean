-- Prove2me | Theorems.Thm_P010_three_mul_prime_mem_class
-- name    : P010.three_mul_prime_mem_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:30:43.814547+00:00
-- url     : https://prove2.me/theorems/01440afa-72b8-4129-8807-48289f11784d
-- title:
--   P010: three mul prime mem class
-- statement:
--   A vertex 3p belongs to class p when p is a prime at least 3.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L955-L963
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L955-L963

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.three_mul_prime_mem_class (n p : ℕ) (hp : Nat.Prime p)
    (hp3 : 3 ≤ p) (hpn : 3 * p ≤ n) :
    3 * p ∈ primeClass n p := by sorry
