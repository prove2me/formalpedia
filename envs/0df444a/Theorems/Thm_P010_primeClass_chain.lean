-- Prove2me | Theorems.Thm_P010_primeClass_chain
-- name    : P010.primeClass_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:35.742278+00:00
-- url     : https://prove2.me/theorems/16a510f9-775d-4f69-9d51-a5aedb2868aa
-- title:
--   P010: prime Class chain
-- statement:
--   Any ordering of a largest-prime-factor class is a noncoprime chain.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L916-L921
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L916-L921

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.primeClass_chain (n p : ℕ) (hp : Nat.Prime p)
    (a : List ℕ) (hclass : ∀ m ∈ a, m ∈ primeClass n p) :
    NonCoprimeChain a := by sorry
