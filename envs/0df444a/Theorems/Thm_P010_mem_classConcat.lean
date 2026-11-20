-- Prove2me | Theorems.Thm_P010_mem_classConcat
-- name    : P010.mem_classConcat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:20.533185+00:00
-- url     : https://prove2.me/theorems/7c4a679c-87aa-4512-a1fb-00d97916cba6
-- title:
--   P010: mem class Concat
-- statement:
--   The P010 construction uses the mem class Concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1739-L1742
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1739-L1742

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.mem_classConcat (n m : ℕ) (ps : List ℕ) :
    m ∈ classConcat n ps ↔
      ∃ p ∈ ps, m ∈ primeClass n p := by sorry
