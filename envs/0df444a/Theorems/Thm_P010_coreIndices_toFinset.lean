-- Prove2me | Theorems.Thm_P010_coreIndices_toFinset
-- name    : P010.coreIndices_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:57.222616+00:00
-- url     : https://prove2.me/theorems/f92a6014-a75d-460a-acbc-f0ad2bb45bab
-- title:
--   P010: core Indices to Finset
-- statement:
--   The P010 construction uses the core Indices to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1846-L1858
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1846-L1858

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.coreIndices_toFinset (n : ℕ) (hn : 12 ≤ n) :
    (coreIndices n).toFinset = (n / 3).primesLE := by sorry
