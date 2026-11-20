-- Prove2me | Theorems.Thm_P010_join_prime_ended_paths
-- name    : P010.join_prime_ended_paths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:29:13.942555+00:00
-- url     : https://prove2.me/theorems/c0b00b23-589c-4cec-8776-deebe9c29ddf
-- title:
--   P010: join prime ended paths
-- statement:
--   A path ending in a multiple of p may be joined to a path
--   starting in a multiple of p.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L253-L260
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L253-L260

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.join_prime_ended_paths (p : ℕ) (hp : Nat.Prime p)
    (a b : List ℕ)
    (ha : NonCoprimeChain a) (hb : NonCoprimeChain b)
    (hend : ∀ x : ℕ, x ∈ a.getLast? → p ∣ x)
    (hstart : ∀ y : ℕ, y ∈ b.head? → p ∣ y) :
    NonCoprimeChain (a ++ b) := by sorry
