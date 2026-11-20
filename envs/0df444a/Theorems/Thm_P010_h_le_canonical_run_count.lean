-- Prove2me | Theorems.Thm_P010_h_le_canonical_run_count
-- name    : P010.h_le_canonical_run_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:43:35.923465+00:00
-- url     : https://prove2.me/theorems/87272aef-5ff5-49c6-ad15-71c3483ce84e
-- title:
--   P010: h le canonical run count
-- statement:
--   The canonical non-coprime-run cover of any permutation
--   gives a valid upper bound on its minimum coprime adjacency count.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L368-L373
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L368-L373

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.h_le_canonical_run_count (n : ℕ) (a : List ℕ)
    (ha : IsPermutation n a) :
    h n ≤ (maximalNonCoprimeRuns a).length - 1 := by sorry
