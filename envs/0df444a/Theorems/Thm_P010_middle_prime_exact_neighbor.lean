-- Prove2me | Theorems.Thm_P010_middle_prime_exact_neighbor
-- name    : P010.middle_prime_exact_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:43:06.217391+00:00
-- url     : https://prove2.me/theorems/b2860f9b-6e60-4b62-bbc2-d507d0eee3dd
-- title:
--   P010: middle prime exact neighbor
-- statement:
--   Every middle prime has exactly one non-coprime neighbor,
--   namely twice itself.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L167-L176
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L167-L176

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.middle_prime_exact_neighbor {n p : ℕ} (hp : Nat.Prime p)
    (hthird : n / 3 < p) (hhalf : p ≤ n / 2) :
    ∃ x : ℕ, 0 < x ∧ x ≤ n ∧ x ≠ p ∧ ¬Nat.Coprime p x ∧
      ∀ y : ℕ, 0 < y → y ≤ n → y ≠ p → ¬Nat.Coprime p y → y = x := by sorry
