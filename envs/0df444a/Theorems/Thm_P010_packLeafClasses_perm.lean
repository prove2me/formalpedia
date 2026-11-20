-- Prove2me | Theorems.Thm_P010_packLeafClasses_perm
-- name    : P010.packLeafClasses_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:37.732754+00:00
-- url     : https://prove2.me/theorems/e92a4174-da15-4b46-9606-bd8c33cda336
-- title:
--   P010: pack Leaf Classes perm
-- statement:
--   Leaf-class packing preserves the multiset of all core vertices
--   and all vertices p,2p from the leaf list.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2061-L2096
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2061-L2096

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.packLeafClasses_perm (core : List ℕ) :
    ∀ leafs : List ℕ,
      (packLeafClasses core leafs).flatten.Perm
        (core ++ leafs.flatMap (fun p => [p, 2 * p])) := by sorry
