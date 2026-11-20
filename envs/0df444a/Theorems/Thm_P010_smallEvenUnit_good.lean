-- Prove2me | Theorems.Thm_P010_smallEvenUnit_good
-- name    : P010.smallEvenUnit_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:34:19.784016+00:00
-- url     : https://prove2.me/theorems/9664c064-674d-4b5c-bd18-f2b99d193f6e
-- title:
--   P010: small Even Unit good
-- statement:
--   Small prime classes admit noncoprime even-ended paths.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1572-L1583
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1572-L1583

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.smallEvenUnit_good (n p : ℕ) (hp : Nat.Prime p)
    (hbound : 4 * p ≤ n) :
    NonCoprimeChain (smallEvenUnit n p) ∧
      EvenEnded (smallEvenUnit n p) := by sorry
