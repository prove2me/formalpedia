-- Prove2me | Theorems.Thm_P010_intermediateEvenUnit_good
-- name    : P010.intermediateEvenUnit_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:24.402228+00:00
-- url     : https://prove2.me/theorems/2362d12c-397d-45dd-b977-257955133134
-- title:
--   P010: intermediate Even Unit good
-- statement:
--   Paired intermediate classes admit noncoprime even-ended paths.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1586-L1609
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1586-L1609

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.intermediateEvenUnit_good (n p q : ℕ) (hn : 12 ≤ n)
    (hp : p ∈ intermediatePrimes n)
    (hq : q ∈ intermediatePrimes n) :
    NonCoprimeChain (intermediateEvenUnit n (p, q)) ∧
      EvenEnded (intermediateEvenUnit n (p, q)) := by sorry
