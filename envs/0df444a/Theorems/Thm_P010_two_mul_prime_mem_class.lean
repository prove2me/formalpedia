-- Prove2me | Theorems.Thm_P010_two_mul_prime_mem_class
-- name    : P010.two_mul_prime_mem_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:28:15.11273+00:00
-- url     : https://prove2.me/theorems/a9f645bb-8efb-4bc2-907f-17e31996490d
-- title:
--   P010: two mul prime mem class
-- statement:
--   The even vertex 2p belongs to the class p when it lies in [2,n].
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L930-L937
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L930-L937

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.two_mul_prime_mem_class (n p : ℕ) (hp : Nat.Prime p)
    (hpn : 2 * p ≤ n) : 2 * p ∈ primeClass n p := by sorry
