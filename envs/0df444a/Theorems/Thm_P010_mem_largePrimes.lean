-- Prove2me | Theorems.Thm_P010_mem_largePrimes
-- name    : P010.mem_largePrimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:27:50.589342+00:00
-- url     : https://prove2.me/theorems/bc66b8dd-cc08-403d-89d5-edf85a2163db
-- title:
--   P010: mem large Primes
-- statement:
--   The P010 construction uses the mem large Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L127-L144
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L127-L144

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.mem_largePrimes {n p : ℕ} :
    p ∈ largePrimes n ↔ Nat.Prime p ∧ n / 2 < p ∧ p ≤ n := by sorry
