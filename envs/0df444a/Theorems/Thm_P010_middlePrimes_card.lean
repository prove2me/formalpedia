-- Prove2me | Theorems.Thm_P010_middlePrimes_card
-- name    : P010.middlePrimes_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:13.323166+00:00
-- url     : https://prove2.me/theorems/18554608-39fc-4bc7-ab35-d7fe0b46aebe
-- title:
--   P010: middle Primes card
-- statement:
--   The P010 construction uses the middle Primes card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L118-L125
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L118-L125

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.middlePrimes_card (n : ℕ) :
    (middlePrimes n).card = pi (n / 2) - pi (n / 3) := by sorry
