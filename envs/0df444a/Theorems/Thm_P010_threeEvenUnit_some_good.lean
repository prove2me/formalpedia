-- Prove2me | Theorems.Thm_P010_threeEvenUnit_some_good
-- name    : P010.threeEvenUnit_some_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:26.26611+00:00
-- url     : https://prove2.me/theorems/d917eeb4-2bbb-40c6-a1da-5e750d8beb79
-- title:
--   P010: three Even Unit some good
-- statement:
--   With one unmatched intermediate class, the prime-3 bridge
--   remains even-ended.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1623-L1643
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1623-L1643

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.threeEvenUnit_some_good (n p : ℕ) (hn : 12 ≤ n)
    (hp : p ∈ intermediatePrimes n) :
    NonCoprimeChain (threeEvenUnit n (some p)) ∧
      EvenEnded (threeEvenUnit n (some p)) := by sorry
