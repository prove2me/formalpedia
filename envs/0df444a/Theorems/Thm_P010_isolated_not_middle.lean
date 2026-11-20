-- Prove2me | Theorems.Thm_P010_isolated_not_middle
-- name    : P010.isolated_not_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:37:34.232644+00:00
-- url     : https://prove2.me/theorems/1ab63ccb-b6f5-42a1-832b-9e1d7bf26db4
-- title:
--   P010: isolated not middle
-- statement:
--   The P010 construction uses the isolated not middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L597-L605
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L597-L605

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.isolated_not_middle (n x : ℕ) (hx : x ∈ isolatedVertices n) :
    x ∉ middlePrimes n := by sorry
