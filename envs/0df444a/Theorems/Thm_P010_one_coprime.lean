-- Prove2me | Theorems.Thm_P010_one_coprime
-- name    : P010.one_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:35:49.127497+00:00
-- url     : https://prove2.me/theorems/70eb7aab-c37c-4b8c-a7a4-f8a8697feb69
-- title:
--   P010: one coprime
-- statement:
--   In the non-coprime graph, the vertex 1 is isolated.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L50-L51
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L50-L51

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.one_coprime (x : ℕ) : Nat.Coprime 1 x := by sorry
