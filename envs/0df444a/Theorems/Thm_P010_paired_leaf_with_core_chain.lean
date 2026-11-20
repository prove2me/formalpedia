-- Prove2me | Theorems.Thm_P010_paired_leaf_with_core_chain
-- name    : P010.paired_leaf_with_core_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:36.554294+00:00
-- url     : https://prove2.me/theorems/8a1010ef-d686-4d73-970d-13dad5b19ebd
-- title:
--   P010: paired leaf with core chain
-- statement:
--   One paired leaf path can absorb the core by inserting it
--   between its two even vertices.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1387-L1411
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1387-L1411

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.paired_leaf_with_core_chain (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (core : List ℕ) (hc : NonCoprimeChain core)
    (he : EvenEnded core) :
    NonCoprimeChain ([p, 2 * p] ++ core ++ [2 * q, q]) := by sorry
