-- Prove2me | Theorems.Thm_P010_join_three_ended_paths
-- name    : P010.join_three_ended_paths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:25.891376+00:00
-- url     : https://prove2.me/theorems/94d5f23d-38e0-40de-84b7-a3e7d604d040
-- title:
--   P010: join three ended paths
-- statement:
--   The same rule for bridges formed by multiples of three.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L271-L276
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L271-L276

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.join_three_ended_paths (a b : List ℕ)
    (ha : NonCoprimeChain a) (hb : NonCoprimeChain b)
    (hend : ∀ x : ℕ, x ∈ a.getLast? → 3 ∣ x)
    (hstart : ∀ y : ℕ, y ∈ b.head? → 3 ∣ y) :
    NonCoprimeChain (a ++ b) := by sorry
