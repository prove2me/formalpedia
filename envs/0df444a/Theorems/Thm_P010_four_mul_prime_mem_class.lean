-- Prove2me | Theorems.Thm_P010_four_mul_prime_mem_class
-- name    : P010.four_mul_prime_mem_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:31.63094+00:00
-- url     : https://prove2.me/theorems/522bd011-db40-4d11-82cf-b476e0605a0e
-- title:
--   P010: four mul prime mem class
-- statement:
--   The even vertex 4p belongs to the class p when it lies in [2,n].
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L940-L952
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L940-L952

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.four_mul_prime_mem_class (n p : ℕ) (hp : Nat.Prime p)
    (hpn : 4 * p ≤ n) : 4 * p ∈ primeClass n p := by sorry
