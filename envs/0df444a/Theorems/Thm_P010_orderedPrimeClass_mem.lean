-- Prove2me | Theorems.Thm_P010_orderedPrimeClass_mem
-- name    : P010.orderedPrimeClass_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:34:17.603198+00:00
-- url     : https://prove2.me/theorems/5129cc7b-2950-4127-a6fc-b3f56739553e
-- title:
--   P010: ordered Prime Class mem
-- statement:
--   The P010 construction uses the ordered Prime Class mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1100-L1112
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1100-L1112

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.orderedPrimeClass_mem (n p u v m : ℕ)
    (hu : u ∈ primeClass n p) (hv : v ∈ primeClass n p)
    (hm : m ∈ orderedPrimeClass n p u v) :
    m ∈ primeClass n p := by sorry
