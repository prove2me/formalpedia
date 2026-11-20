-- Prove2me | Theorems.Thm_P010_primeClass_prime
-- name    : P010.primeClass_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:46:16.556174+00:00
-- url     : https://prove2.me/theorems/6440415d-e00c-463b-b896-ba6276b36dd6
-- title:
--   P010: prime Class prime
-- statement:
--   The P010 construction uses the prime Class prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L880-L884
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L880-L884

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.primeClass_prime {n p m : ℕ} (hm : m ∈ primeClass n p) :
    Nat.Prime p := by sorry
