-- Prove2me | Theorems.Thm_P010_isolated_path_singleton
-- name    : P010.isolated_path_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:33:35.7675+00:00
-- url     : https://prove2.me/theorems/3169e363-2fac-46a8-818c-96963a0ff58c
-- title:
--   P010: isolated path singleton
-- statement:
--   A marked isolated vertex forces its entire non-coprime path
--   to be a singleton.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L708-L715
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L708-L715

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.isolated_path_singleton (n p : ℕ) (a : List ℕ)
    (hi : p ∈ isolatedVertices n) (hc : NonCoprimeChain a)
    (hd : a.Nodup) (hp : p ∈ a)
    (hb : ∀ t ∈ a, 0 < t ∧ t ≤ n) : a = [p] := by sorry
