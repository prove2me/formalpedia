-- Prove2me | Theorems.Thm_P010_unpaired_leaf_with_core_chain
-- name    : P010.unpaired_leaf_with_core_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:34:14.417434+00:00
-- url     : https://prove2.me/theorems/36ef0226-b0e4-49e0-aba2-4daaefe66671
-- title:
--   P010: unpaired leaf with core chain
-- statement:
--   An unmatched leaf class may be attached to the even-ended
--   core path, with no use of prime-counting estimates.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1370-L1383
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1370-L1383

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.unpaired_leaf_with_core_chain (p : ℕ) (hp : Nat.Prime p)
    (core : List ℕ) (hc : NonCoprimeChain core)
    (he : EvenEnded core) :
    NonCoprimeChain ([p, 2 * p] ++ core) := by sorry
