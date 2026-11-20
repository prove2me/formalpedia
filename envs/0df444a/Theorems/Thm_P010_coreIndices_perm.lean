-- Prove2me | Theorems.Thm_P010_coreIndices_perm
-- name    : P010.coreIndices_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:01.226287+00:00
-- url     : https://prove2.me/theorems/a1d55e47-7391-49b3-bae1-bcd128dd22c6
-- title:
--   P010: core Indices perm
-- statement:
--   The core prime-index list is a permutation of all primes ≤ n/3.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1861-L1866
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1861-L1866

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.coreIndices_perm (n : ℕ) (hn : 12 ≤ n) :
    (coreIndices n).Perm (n / 3).primesLE.toList := by sorry
