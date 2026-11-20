-- Prove2me | Theorems.Thm_P010_small_intermediate_partition
-- name    : P010.small_intermediate_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:50.428554+00:00
-- url     : https://prove2.me/theorems/830f2538-030f-4473-b696-606b867a20ba
-- title:
--   P010: small intermediate partition
-- statement:
--   Small and intermediate primes partition the primes at most n/3.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1783-L1795
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1783-L1795

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.small_intermediate_partition (n : ℕ) :
    (n / 4).primesLE ∪ intermediatePrimes n =
      (n / 3).primesLE := by sorry
