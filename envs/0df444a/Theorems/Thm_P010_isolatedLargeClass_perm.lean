-- Prove2me | Theorems.Thm_P010_isolatedLargeClass_perm
-- name    : P010.isolatedLargeClass_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:59.084179+00:00
-- url     : https://prove2.me/theorems/d12ece27-7d0f-4868-b91c-7cd96fa11a6b
-- title:
--   P010: isolated Large Class perm
-- statement:
--   The singleton large-prime path enumerates its class.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2124-L2128
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2124-L2128

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.isolatedLargeClass_perm (n p : ℕ) (hp : p ∈ largePrimes n) :
    ([p] : List ℕ).Perm (primeClass n p).toList := by sorry
