-- Prove2me | Theorems.Thm_P010_range_one_perm_Icc
-- name    : P010.range_one_perm_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:09.456439+00:00
-- url     : https://prove2.me/theorems/2af46538-1010-4eb9-b5c4-bf9af0e0be88
-- title:
--   P010: range one perm Icc
-- statement:
--   The P010 construction uses the range one perm Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1895-L1900
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1895-L1900

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.range_one_perm_Icc (n : ℕ) :
    (List.range' 1 n).Perm (Finset.Icc 1 n).toList := by sorry
