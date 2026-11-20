-- Prove2me | Theorems.Thm_P010_prime_mem_primeClass
-- name    : P010.prime_mem_primeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:30:47.635703+00:00
-- url     : https://prove2.me/theorems/5bb21731-0131-4ba8-a6b4-2c496e6f589f
-- title:
--   P010: prime mem prime Class
-- statement:
--   A prime occurs in its own class whenever it does not exceed n.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L924-L927
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L924-L927

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.prime_mem_primeClass (n p : ℕ) (hp : Nat.Prime p)
    (hpn : p ≤ n) : p ∈ primeClass n p := by sorry
