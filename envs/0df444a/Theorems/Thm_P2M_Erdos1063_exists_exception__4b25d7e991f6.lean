-- Prove2me | Theorems.Thm_P2M_Erdos1063_exists_exception__4b25d7e991f6
-- name    : P2M_Erdos1063_exists_exception__4b25d7e991f6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:39:20.023437+00:00
-- url     : https://prove2.me/theorems/62a3c928-43d6-5d06-801c-64101f936e22
-- title:
--   P2 M Erdos1063 exists exception  4b25d7e991f6: P2 M Erdos1063 exists exception  4b25d7e991f6
-- statement:
--   **Erdős–Selfridge.** Not every element of the block divides `n.choose k`
--   (derived from `valuation_bound`: a prime `p ∣ k` would have to divide both `n` and `n - 1`).
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L405-L418
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L405-L418

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem P2M_Erdos1063_exists_exception__4b25d7e991f6 {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n) :
    ¬ ∀ i < k, (n - i) ∣ n.choose k := by sorry

alias «Erdos1063».«exists_exception'» := P2M_Erdos1063_exists_exception__4b25d7e991f6
