-- Prove2me | Theorems.Thm_P010_maximalNonCoprimeRuns_flatten
-- name    : P010.maximalNonCoprimeRuns_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:56.185363+00:00
-- url     : https://prove2.me/theorems/c7d19ca1-0113-4b6e-9129-53d2d6f6ac65
-- title:
--   P010: maximal Non Coprime Runs flatten
-- statement:
--   Splitting at coprime adjacencies never removes or duplicates vertices.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L351-L353
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L351-L353

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.maximalNonCoprimeRuns_flatten (a : List ℕ) :
    (maximalNonCoprimeRuns a).flatten = a := by sorry
