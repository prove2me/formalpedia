-- Prove2me | Theorems.Thm_P010_orderedPrimeClass_perm
-- name    : P010.orderedPrimeClass_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:31:27.780278+00:00
-- url     : https://prove2.me/theorems/972f4460-89a8-4f45-9f01-be39699d9650
-- title:
--   P010: ordered Prime Class perm
-- statement:
--   A prescribed-endpoint ordering is a permutation of the class list.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1170-L1178
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1170-L1178

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.orderedPrimeClass_perm (n p u v : ℕ)
    (hu : u ∈ primeClass n p) (hv : v ∈ primeClass n p)
    (huv : u ≠ v) :
    (orderedPrimeClass n p u v).Perm (primeClass n p).toList := by sorry
