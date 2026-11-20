-- Prove2me | Theorems.Thm_P010_large_prime_isolated
-- name    : P010.large_prime_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:36:00.286618+00:00
-- url     : https://prove2.me/theorems/5e485f1b-47aa-4f5b-bfc0-1ee2bb103d7e
-- title:
--   P010: large prime isolated
-- statement:
--   A prime above `n/2` has no non-coprime neighbor distinct
--   from itself among positive integers at most `n`.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L55-L74
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L55-L74

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.large_prime_isolated {n p x : ℕ} (hp : Nat.Prime p)
    (hbig : n / 2 < p) (hxpos : 0 < x) (hxle : x ≤ n)
    (hne : x ≠ p) : Nat.Coprime p x := by sorry
