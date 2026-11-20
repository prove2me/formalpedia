-- Prove2me | Theorems.Thm_P010_range_one_toFinset
-- name    : P010.range_one_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:11.143154+00:00
-- url     : https://prove2.me/theorems/ab7edf40-a227-4d51-93c5-36baecc6e912
-- title:
--   P010: range one to Finset
-- statement:
--   The P010 construction uses the range one to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1881-L1893
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1881-L1893

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.range_one_toFinset (n : ℕ) :
    (List.range' 1 n).toFinset = Finset.Icc 1 n := by sorry
