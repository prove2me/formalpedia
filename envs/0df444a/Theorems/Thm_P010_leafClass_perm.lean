-- Prove2me | Theorems.Thm_P010_leafClass_perm
-- name    : P010.leafClass_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:34.768816+00:00
-- url     : https://prove2.me/theorems/0363eaeb-4116-42f2-8cb5-c4dd5f9a41cf
-- title:
--   P010: leaf Class perm
-- statement:
--   The two-vertex list of a middle-range prime enumerates its class.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2104-L2113
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2104-L2113

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.leafClass_perm (n p : ℕ) (hp : p ∈ middlePrimes n) :
    ([p, 2 * p] : List ℕ).Perm (primeClass n p).toList := by sorry
