-- Prove2me | Theorems.Thm_P010_largePrimes_card
-- name    : P010.largePrimes_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:32.310517+00:00
-- url     : https://prove2.me/theorems/366bd13f-62c1-4c49-b8f3-4aa6a09c9a40
-- title:
--   P010: large Primes card
-- statement:
--   The P010 construction uses the large Primes card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L109-L116
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L109-L116

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.largePrimes_card (n : ℕ) :
    (largePrimes n).card = pi n - pi (n / 2) := by sorry
