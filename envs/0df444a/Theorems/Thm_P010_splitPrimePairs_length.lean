-- Prove2me | Theorems.Thm_P010_splitPrimePairs_length
-- name    : P010.splitPrimePairs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:48:46.495501+00:00
-- url     : https://prove2.me/theorems/ebd8cc4e-1ec7-4eed-97b8-f7a50c92ae29
-- title:
--   P010: split Prime Pairs length
-- statement:
--   The number of paired items in a split is exactly twice the
--   number of resulting pairs, with one additional item if unmatched.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1514-L1523
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1514-L1523

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.splitPrimePairs_length (ps : List ℕ) :
    2 * (splitPrimePairs ps).1.length +
      (splitPrimePairs ps).2.toList.length = ps.length := by sorry
