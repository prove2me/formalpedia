-- Prove2me | Theorems.Thm_P010_leaf_left_chain
-- name    : P010.leaf_left_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:10.856187+00:00
-- url     : https://prove2.me/theorems/94f63053-1a43-4ada-9660-3ae638d6325d
-- title:
--   P010: leaf left chain
-- statement:
--   For any prime p, the two-vertex leaf path p--2p is
--   a simple noncoprime chain ending at an even vertex.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1339-L1343
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1339-L1343

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.leaf_left_chain (p : ℕ) (hp : Nat.Prime p) :
    NonCoprimeChain [p, 2 * p] := by sorry
