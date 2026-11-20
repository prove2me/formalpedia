-- Prove2me | Theorems.Thm_P010_smallEvenUnit_perm
-- name    : P010.smallEvenUnit_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:35:26.640575+00:00
-- url     : https://prove2.me/theorems/5abe345c-4b2a-409c-8604-a810b14e0d16
-- title:
--   P010: small Even Unit perm
-- statement:
--   Small-class units enumerate their whole class exactly once.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1904-L1908
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1904-L1908

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.smallEvenUnit_perm (n p : ℕ) (hp : Nat.Prime p)
    (hbound : 4 * p ≤ n) :
    (smallEvenUnit n p).Perm (primeClass n p).toList := by sorry
