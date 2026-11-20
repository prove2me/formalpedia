-- Prove2me | Theorems.Thm_P010_threeEvenUnit_some_perm
-- name    : P010.threeEvenUnit_some_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:36.228193+00:00
-- url     : https://prove2.me/theorems/686af1be-5e3c-40ce-92c5-c2a0bda5d352
-- title:
--   P010: three Even Unit some perm
-- statement:
--   The prime-3 bridge with one unmatched class enumerates both
--   classes exactly once.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1937-L1947
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1937-L1947

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.threeEvenUnit_some_perm (n p : ℕ) (hn : 12 ≤ n)
    (hp : p ∈ intermediatePrimes n) :
    (threeEvenUnit n (some p)).Perm (classConcat n [3, p]) := by sorry
