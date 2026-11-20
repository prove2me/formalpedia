-- Prove2me | Theorems.Thm_P010_primeClass_toList_disjoint
-- name    : P010.primeClass_toList_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:29.037645+00:00
-- url     : https://prove2.me/theorems/5435ce82-9b19-410b-b52b-63e96f9d3ba5
-- title:
--   P010: prime Class to List disjoint
-- statement:
--   Distinct prime-factor classes have disjoint vertex lists.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1745-L1751
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1745-L1751

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.primeClass_toList_disjoint (n p q : ℕ) (hpq : p ≠ q) :
    List.Disjoint (primeClass n p).toList (primeClass n q).toList := by sorry
