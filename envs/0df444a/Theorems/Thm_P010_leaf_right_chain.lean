-- Prove2me | Theorems.Thm_P010_leaf_right_chain
-- name    : P010.leaf_right_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:24.692072+00:00
-- url     : https://prove2.me/theorems/75b4bb2a-eb90-4f2c-94e6-eee2c32ced40
-- title:
--   P010: leaf right chain
-- statement:
--   The reverse leaf class ends at the prime vertex p.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1346-L1350
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1346-L1350

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.leaf_right_chain (p : ℕ) (hp : Nat.Prime p) :
    NonCoprimeChain [2 * p, p] := by sorry
