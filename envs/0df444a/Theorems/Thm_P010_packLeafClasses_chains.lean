-- Prove2me | Theorems.Thm_P010_packLeafClasses_chains
-- name    : P010.packLeafClasses_chains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:36.742825+00:00
-- url     : https://prove2.me/theorems/1d8c2b14-f573-4486-b2c4-303d9f2db00d
-- title:
--   P010: pack Leaf Classes chains
-- statement:
--   Every packed leaf component is a noncoprime path when the
--   core is an even-ended noncoprime path.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1447-L1486
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1447-L1486

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.packLeafClasses_chains (core : List ℕ)
    (hc : NonCoprimeChain core) (he : EvenEnded core) :
    ∀ (leafs : List ℕ),
      (∀ p ∈ leafs, Nat.Prime p) →
      ∀ path ∈ packLeafClasses core leafs, NonCoprimeChain path := by sorry
