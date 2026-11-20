-- Prove2me | Theorems.Thm_P010_maximalNonCoprimeRuns_length
-- name    : P010.maximalNonCoprimeRuns_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:36:41.618322+00:00
-- url     : https://prove2.me/theorems/1f70aded-9e0a-4212-9d85-85bcf4447f06
-- title:
--   P010: maximal Non Coprime Runs length
-- statement:
--   The number of maximal non-coprime runs is exactly one more
--   than the number of adjacent coprime pairs.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L401-L405
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L401-L405

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.maximalNonCoprimeRuns_length (x : ℕ) (xs : List ℕ) :
    (maximalNonCoprimeRuns (x :: xs)).length =
      adjacentCount (x :: xs) + 1 := by sorry
