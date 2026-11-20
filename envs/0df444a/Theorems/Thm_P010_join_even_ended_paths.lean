-- Prove2me | Theorems.Thm_P010_join_even_ended_paths
-- name    : P010.join_even_ended_paths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:36:00.335208+00:00
-- url     : https://prove2.me/theorems/9d732c3d-99e0-4cef-a2ef-60c800ca2a01
-- title:
--   P010: join even ended paths
-- statement:
--   The proof's even-endpoint concatenation rule (p = 2).
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L263-L268
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L263-L268

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.join_even_ended_paths (a b : List ℕ)
    (ha : NonCoprimeChain a) (hb : NonCoprimeChain b)
    (hend : ∀ x : ℕ, x ∈ a.getLast? → 2 ∣ x)
    (hstart : ∀ y : ℕ, y ∈ b.head? → 2 ∣ y) :
    NonCoprimeChain (a ++ b) := by sorry
