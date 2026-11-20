-- Prove2me | Theorems.Thm_P010_primeClass_multiple_below
-- name    : P010.primeClass_multiple_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:31:07.312194+00:00
-- url     : https://prove2.me/theorems/1531cdd6-08a6-44db-8e76-780d3ec2a195
-- title:
--   P010: prime Class multiple below
-- statement:
--   An element of class p bounded by k*p has multiplier in [1,k).
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L994-L1012
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L994-L1012

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.primeClass_multiple_below (n p m k : ℕ)
    (hm : m ∈ primeClass n p) (hupper : n < k * p) :
    ∃ t : ℕ, 1 ≤ t ∧ t < k ∧ m = t * p := by sorry
