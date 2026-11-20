-- Prove2me | Theorems.Thm_P010_one_path_singleton
-- name    : P010.one_path_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:37:17.910405+00:00
-- url     : https://prove2.me/theorems/58e48e31-379c-492f-94a7-9e6d20235e6c
-- title:
--   P010: one path singleton
-- statement:
--   The vertex 1 is a singleton in any simple non-coprime path
--   containing it.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L556-L561
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L556-L561

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.one_path_singleton (a : List ℕ)
    (hchain : NonCoprimeChain a) (hnodup : a.Nodup)
    (hmem : 1 ∈ a) : a = [1] := by sorry
