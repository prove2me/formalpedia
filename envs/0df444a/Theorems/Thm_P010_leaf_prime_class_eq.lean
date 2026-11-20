-- Prove2me | Theorems.Thm_P010_leaf_prime_class_eq
-- name    : P010.leaf_prime_class_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:36.831893+00:00
-- url     : https://prove2.me/theorems/4bdc603c-7b42-4e06-9dbb-aed81d1f96c9
-- title:
--   P010: leaf prime class eq
-- statement:
--   In (n/3,n/2] the class has exactly the prime and its double.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1032-L1050
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1032-L1050

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.leaf_prime_class_eq (n p : ℕ) (hp : Nat.Prime p)
    (hthird : n / 3 < p) (hhalf : p ≤ n / 2) :
    primeClass n p = {p, 2 * p} := by sorry
