-- Prove2me | Theorems.Thm_P010_splitPrimePairs_pair_mem
-- name    : P010.splitPrimePairs_pair_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:34:46.509761+00:00
-- url     : https://prove2.me/theorems/817a74f5-097d-4b87-97c9-38724f765844
-- title:
--   P010: split Prime Pairs pair mem
-- statement:
--   Every member of a pair produced by splitting belongs to the
--   original list.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1648-L1664
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1648-L1664

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.splitPrimePairs_pair_mem (ps : List ℕ) (pair : ℕ × ℕ)
    (hp : pair ∈ (splitPrimePairs ps).1) :
    pair.1 ∈ ps ∧ pair.2 ∈ ps := by sorry
