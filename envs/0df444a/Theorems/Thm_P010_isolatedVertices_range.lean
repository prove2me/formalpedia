-- Prove2me | Theorems.Thm_P010_isolatedVertices_range
-- name    : P010.isolatedVertices_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:37:37.527643+00:00
-- url     : https://prove2.me/theorems/a2e68668-d89b-47c9-9552-b63991f16a5c
-- title:
--   P010: isolated Vertices range
-- statement:
--   The P010 construction uses the isolated Vertices range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L583-L589
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L583-L589

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.isolatedVertices_range (n x : ℕ) (hx : x ∈ isolatedVertices n)
    (hn : 1 ≤ n) : 1 ≤ x ∧ x ≤ n := by sorry
