-- Prove2me | Theorems.Thm_P010_P010_universal_lower_bound
-- name    : P010.P010_universal_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:04.840897+00:00
-- url     : https://prove2.me/theorems/3dbc9e99-9df7-4778-b4f5-cdd5a17a0271
-- title:
--   P010: P010 universal lower bound
-- statement:
--   The universal lower bound in P010. No assertion about the
--   constructive upper bound is used.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L825-L846
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L825-L846

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.P010_universal_lower_bound (n : ℕ) (hn : 4 ≤ n)
    (a : List ℕ) (ha : IsPermutation n a) :
    target n ≤ adjacentCount a := by sorry
