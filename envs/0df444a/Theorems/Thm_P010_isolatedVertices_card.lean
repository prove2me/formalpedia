-- Prove2me | Theorems.Thm_P010_isolatedVertices_card
-- name    : P010.isolatedVertices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:37:30.344793+00:00
-- url     : https://prove2.me/theorems/3cf59574-4c9e-4cbf-8457-52dc86cb6ace
-- title:
--   P010: isolated Vertices card
-- statement:
--   The P010 construction uses the isolated Vertices card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L579-L581
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L579-L581

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.isolatedVertices_card (n : ℕ) :
    (isolatedVertices n).card = pi n - pi (n / 2) + 1 := by sorry
