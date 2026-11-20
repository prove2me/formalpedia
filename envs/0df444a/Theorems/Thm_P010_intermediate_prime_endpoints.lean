-- Prove2me | Theorems.Thm_P010_intermediate_prime_endpoints
-- name    : P010.intermediate_prime_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:29:39.40268+00:00
-- url     : https://prove2.me/theorems/daf08b67-2b29-4d90-9f28-02726fa87fd6
-- title:
--   P010: intermediate prime endpoints
-- statement:
--   Prime classes in the intermediate interval possess one even
--   and one divisible-by-three endpoint.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L979-L990
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L979-L990

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.intermediate_prime_endpoints (n p : ℕ) (hn : 12 ≤ n)
    (hp : Nat.Prime p) (hquarter : n / 4 < p)
    (hthird : p ≤ n / 3) :
    2 * p ∈ primeClass n p ∧
      3 * p ∈ primeClass n p ∧ 2 * p ≠ 3 * p := by sorry
