-- Prove2me | Theorems.Thm_P010_intermediatePrimes_card
-- name    : P010.intermediatePrimes_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:47:28.31306+00:00
-- url     : https://prove2.me/theorems/e30b2c77-3202-4cf2-aac9-5439be6b5639
-- title:
--   P010: intermediate Primes card
-- statement:
--   The P010 construction uses the intermediate Primes card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1242-L1249
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1242-L1249

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.intermediatePrimes_card (n : ℕ) :
    (intermediatePrimes n).card = pi (n / 3) - pi (n / 4) := by sorry
