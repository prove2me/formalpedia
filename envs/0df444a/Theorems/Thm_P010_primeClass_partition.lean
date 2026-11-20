-- Prove2me | Theorems.Thm_P010_primeClass_partition
-- name    : P010.primeClass_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:29.063625+00:00
-- url     : https://prove2.me/theorems/255791d1-60e7-46ea-a5aa-179f94d2aca4
-- title:
--   P010: prime Class partition
-- statement:
--   The classes indexed by primes at most n cover every integer in [2,n].
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L887-L904
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L887-L904

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.primeClass_partition (n : ℕ) :
    (n.primesLE.biUnion (fun p => primeClass n p)) = Finset.Icc 2 n := by sorry
