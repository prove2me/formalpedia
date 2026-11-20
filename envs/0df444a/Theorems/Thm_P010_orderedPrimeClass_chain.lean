-- Prove2me | Theorems.Thm_P010_orderedPrimeClass_chain
-- name    : P010.orderedPrimeClass_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:31:27.545763+00:00
-- url     : https://prove2.me/theorems/5c98cf59-9396-4074-baff-87df1cdcc6a8
-- title:
--   P010: ordered Prime Class chain
-- statement:
--   The prescribed-endpoint class ordering is a noncoprime chain.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1148-L1154
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1148-L1154

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.orderedPrimeClass_chain (n p u v : ℕ)
    (hp : Nat.Prime p)
    (hu : u ∈ primeClass n p) (hv : v ∈ primeClass n p) :
    NonCoprimeChain (orderedPrimeClass n p u v) := by sorry
