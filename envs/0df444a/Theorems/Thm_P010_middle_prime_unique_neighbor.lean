-- Prove2me | Theorems.Thm_P010_middle_prime_unique_neighbor
-- name    : P010.middle_prime_unique_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:08.131549+00:00
-- url     : https://prove2.me/theorems/d8a917ed-d6bb-48f6-b852-9af8a64c3331
-- title:
--   P010: middle prime unique neighbor
-- statement:
--   A prime between `n/3` and `n/2` has at most one
--   possible non-coprime neighbor: `2p`.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L78-L98
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L78-L98

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.middle_prime_unique_neighbor {n p x : ℕ} (hp : Nat.Prime p)
    (hthird : n / 3 < p) (hxpos : 0 < x) (hxle : x ≤ n)
    (hne : x ≠ p) (hnoncoprime : ¬Nat.Coprime p x) : x = 2 * p := by sorry
