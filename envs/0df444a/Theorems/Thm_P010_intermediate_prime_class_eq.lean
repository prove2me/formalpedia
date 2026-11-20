-- Prove2me | Theorems.Thm_P010_intermediate_prime_class_eq
-- name    : P010.intermediate_prime_class_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:47:17.822239+00:00
-- url     : https://prove2.me/theorems/8342dec8-c7b2-4f4a-b361-96938bc78bdd
-- title:
--   P010: intermediate prime class eq
-- statement:
--   In (n/4,n/3] the class consists of p, 2p, and 3p for n≥12.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1053-L1076
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1053-L1076

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.intermediate_prime_class_eq (n p : ℕ) (hn : 12 ≤ n)
    (hp : Nat.Prime p) (hquarter : n / 4 < p)
    (hthird : p ≤ n / 3) :
    primeClass n p = {p, 2 * p, 3 * p} := by sorry
