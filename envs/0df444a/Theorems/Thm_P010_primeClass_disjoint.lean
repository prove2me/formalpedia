-- Prove2me | Theorems.Thm_P010_primeClass_disjoint
-- name    : P010.primeClass_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:25.097896+00:00
-- url     : https://prove2.me/theorems/8033b894-7e41-41ad-8fa2-cee976573ebd
-- title:
--   P010: prime Class disjoint
-- statement:
--   Different largest-prime-factor classes have no common member.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L907-L913
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L907-L913

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.primeClass_disjoint (n p q : ℕ) (hpq : p ≠ q) :
    Disjoint (primeClass n p) (primeClass n q) := by sorry
