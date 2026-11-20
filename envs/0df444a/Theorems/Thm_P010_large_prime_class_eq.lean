-- Prove2me | Theorems.Thm_P010_large_prime_class_eq
-- name    : P010.large_prime_class_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:35.988519+00:00
-- url     : https://prove2.me/theorems/2c0d6c9f-c19d-421c-89c6-d0e4543bfb92
-- title:
--   P010: large prime class eq
-- statement:
--   Above n/2 the largest-prime-factor class is a singleton.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1015-L1029
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1015-L1029

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.large_prime_class_eq (n p : ℕ) (hp : Nat.Prime p)
    (hbig : n / 2 < p) (hle : p ≤ n) :
    primeClass n p = {p} := by sorry
