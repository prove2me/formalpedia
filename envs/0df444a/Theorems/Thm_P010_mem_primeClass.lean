-- Prove2me | Theorems.Thm_P010_mem_primeClass
-- name    : P010.mem_primeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:27:52.878217+00:00
-- url     : https://prove2.me/theorems/ef8a8115-0b35-43a7-a1e3-2f40dd911205
-- title:
--   P010: mem prime Class
-- statement:
--   The P010 construction uses the mem prime Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L871-L873
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L871-L873

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.mem_primeClass {n p m : ℕ} :
    m ∈ primeClass n p ↔ 2 ≤ m ∧ m ≤ n ∧ Nat.maxPrimeFac m = p := by sorry
