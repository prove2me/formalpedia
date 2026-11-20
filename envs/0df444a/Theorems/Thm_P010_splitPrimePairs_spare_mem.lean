-- Prove2me | Theorems.Thm_P010_splitPrimePairs_spare_mem
-- name    : P010.splitPrimePairs_spare_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:35:03.290616+00:00
-- url     : https://prove2.me/theorems/744fa9cd-6f03-47da-8a8c-8859e61300fc
-- title:
--   P010: split Prime Pairs spare mem
-- statement:
--   The optional unmatched element of a split belongs to its input.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1667-L1672
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1667-L1672

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.splitPrimePairs_spare_mem (ps : List ℕ) (p : ℕ)
    (hp : (splitPrimePairs ps).2 = some p) : p ∈ ps := by sorry
