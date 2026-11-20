-- Prove2me | Theorems.Thm_P010_paired_leaf_classes_chain
-- name    : P010.paired_leaf_classes_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:34.977651+00:00
-- url     : https://prove2.me/theorems/e5777003-7bc5-4160-8861-cffd3f9fb325
-- title:
--   P010: paired leaf classes chain
-- statement:
--   Two distinct leaf-prime classes can form a noncoprime path
--   without using any vertex of the even-ended core.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1354-L1366
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1354-L1366

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.paired_leaf_classes_chain (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    NonCoprimeChain [p, 2 * p, 2 * q, q] := by sorry
