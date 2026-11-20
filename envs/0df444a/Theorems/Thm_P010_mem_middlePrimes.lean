-- Prove2me | Theorems.Thm_P010_mem_middlePrimes
-- name    : P010.mem_middlePrimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:28:05.763488+00:00
-- url     : https://prove2.me/theorems/c45bddc1-8336-4f3f-82f9-bfad8d567742
-- title:
--   P010: mem middle Primes
-- statement:
--   The P010 construction uses the mem middle Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L146-L163
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L146-L163

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.mem_middlePrimes {n p : ℕ} :
    p ∈ middlePrimes n ↔ Nat.Prime p ∧ n / 3 < p ∧ p ≤ n / 2 := by sorry
