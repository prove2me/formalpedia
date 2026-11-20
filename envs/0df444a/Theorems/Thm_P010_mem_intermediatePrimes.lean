-- Prove2me | Theorems.Thm_P010_mem_intermediatePrimes
-- name    : P010.mem_intermediatePrimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:27:53.287024+00:00
-- url     : https://prove2.me/theorems/0e940d7a-4119-4472-9f99-8f9344bb72fc
-- title:
--   P010: mem intermediate Primes
-- statement:
--   The P010 construction uses the mem intermediate Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1251-L1268
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1251-L1268

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.mem_intermediatePrimes {n p : ℕ} :
    p ∈ intermediatePrimes n ↔
      Nat.Prime p ∧ n / 4 < p ∧ p ≤ n / 3 := by sorry
