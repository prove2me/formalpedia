-- Prove2me | Theorems.Thm_P010_primeClass_dvd
-- name    : P010.primeClass_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:33:19.959322+00:00
-- url     : https://prove2.me/theorems/dae4b750-084c-43ac-bdc9-e122ee488bff
-- title:
--   P010: prime Class dvd
-- statement:
--   The P010 construction uses the prime Class dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L875-L878
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L875-L878

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.primeClass_dvd {n p m : ℕ} (hm : m ∈ primeClass n p) :
    p ∣ m := by sorry
