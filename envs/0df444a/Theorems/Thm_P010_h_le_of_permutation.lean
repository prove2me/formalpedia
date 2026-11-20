-- Prove2me | Theorems.Thm_P010_h_le_of_permutation
-- name    : P010.h_le_of_permutation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:30:09.316202+00:00
-- url     : https://prove2.me/theorems/509e7889-6127-4cdd-a9a4-e6f6bf3a7fa2
-- title:
--   P010: h le of permutation
-- statement:
--   The P010 construction uses the h le of permutation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L27-L30
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L27-L30

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.h_le_of_permutation (n : ℕ) (a : List ℕ) (ha : IsPermutation n a) :
    h n ≤ adjacentCount a := by sorry
