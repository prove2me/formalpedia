-- Prove2me | Theorems.Thm_P010_corePath_perm_classConcat
-- name    : P010.corePath_perm_classConcat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:35:21.956651+00:00
-- url     : https://prove2.me/theorems/10eb1dd2-2ad1-4509-abf6-aab43fb0a0d8
-- title:
--   P010: core Path perm class Concat
-- statement:
--   The complete core path is a permutation of the concatenated
--   classes indexed by all primes at most n/3.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1988-L2049
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1988-L2049

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.corePath_perm_classConcat (n : ℕ) (hn : 12 ≤ n) :
    (corePath n).Perm (classConcat n (n / 3).primesLE.toList) := by sorry
