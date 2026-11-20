-- Prove2me | Theorems.Thm_P010_orderedPrimeClass_toFinset
-- name    : P010.orderedPrimeClass_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:51.65955+00:00
-- url     : https://prove2.me/theorems/d3bba224-a902-437e-a2cf-d3c350f7abd2
-- title:
--   P010: ordered Prime Class to Finset
-- statement:
--   The prescribed-endpoint ordering covers precisely its class.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1115-L1130
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1115-L1130

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.orderedPrimeClass_toFinset (n p u v : ℕ)
    (hu : u ∈ primeClass n p) (hv : v ∈ primeClass n p) :
    (orderedPrimeClass n p u v).toFinset = primeClass n p := by sorry
