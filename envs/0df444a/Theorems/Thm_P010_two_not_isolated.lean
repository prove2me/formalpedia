-- Prove2me | Theorems.Thm_P010_two_not_isolated
-- name    : P010.two_not_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:12.195678+00:00
-- url     : https://prove2.me/theorems/2472543d-55c1-4a19-9205-42032e95b460
-- title:
--   P010: two not isolated
-- statement:
--   The P010 construction uses the two not isolated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L607-L613
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L607-L613

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.two_not_isolated (n : ℕ) (hn : 4 ≤ n) :
    2 ∉ isolatedVertices n := by sorry
