-- Prove2me | Theorems.Thm_P010_adjacentCount_append_le
-- name    : P010.adjacentCount_append_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:36:20.152191+00:00
-- url     : https://prove2.me/theorems/3694d61d-6f9a-432a-8e69-80a48fe41bb7
-- title:
--   P010: adjacent Count append le
-- statement:
--   Joining two lists introduces at most one new coprime adjacency.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L289-L308
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L289-L308

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.adjacentCount_append_le (a b : List ℕ) :
    adjacentCount (a ++ b) ≤
      adjacentCount a + adjacentCount b + 1 := by sorry
