-- Prove2me | Theorems.Thm_P010_permutation_mem_iff
-- name    : P010.permutation_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:30:12.569194+00:00
-- url     : https://prove2.me/theorems/651ea37e-6f91-46d0-842d-3c6c9f47399f
-- title:
--   P010: permutation mem iff
-- statement:
--   Membership in [1,n] for an arbitrary valid permutation.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L616-L628
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L616-L628

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.permutation_mem_iff (n : ℕ) (a : List ℕ)
    (ha : IsPermutation n a) (x : ℕ) :
    x ∈ a ↔ 1 ≤ x ∧ x ≤ n := by sorry
