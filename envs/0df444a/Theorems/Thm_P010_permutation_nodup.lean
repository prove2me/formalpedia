-- Prove2me | Theorems.Thm_P010_permutation_nodup
-- name    : P010.permutation_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:59.63719+00:00
-- url     : https://prove2.me/theorems/9f93d79f-d2b7-4a11-b98b-5361ea9c92f6
-- title:
--   P010: permutation nodup
-- statement:
--   The P010 construction uses the permutation nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L630-L632
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L630-L632

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.permutation_nodup (n : ℕ) (a : List ℕ)
    (ha : IsPermutation n a) : a.Nodup := by sorry
