-- Prove2me | Theorems.Thm_P010_splitPrimePairs_recompose
-- name    : P010.splitPrimePairs_recompose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:31:38.091286+00:00
-- url     : https://prove2.me/theorems/61b2f726-bfde-4b26-a502-b977dadd8169
-- title:
--   P010: split Prime Pairs recompose
-- statement:
--   The pair splitting loses no elements: unfolding the pairs and
--   optional leftover reproduces the input list in its original order.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1500-L1510
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1500-L1510

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.splitPrimePairs_recompose :
    ∀ ps : List ℕ,
      (splitPrimePairs ps).1.flatMap (fun pq => [pq.1, pq.2]) ++
        (splitPrimePairs ps).2.toList = ps := by sorry
