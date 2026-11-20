-- Prove2me | Theorems.Thm_P010_middle_primes_path_capacity
-- name    : P010.middle_primes_path_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:36:59.118763+00:00
-- url     : https://prove2.me/theorems/cbc3c90a-9d65-4363-a8d4-af12b870f507
-- title:
--   P010: middle primes path capacity
-- statement:
--   A simple non-coprime path contains at most two primes from
--   the degree-one interval (n/3,n/2]. The two can only be endpoints.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L466-L486
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L466-L486

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.middle_primes_path_capacity (n : ℕ) (a : List ℕ)
    (hchain : NonCoprimeChain a)
    (hnodup : a.Nodup)
    (hbound : ∀ t ∈ a, 0 < t ∧ t ≤ n) :
    (a.filter (fun t => decide (t ∈ middlePrimes n))).length ≤ 2 := by sorry
