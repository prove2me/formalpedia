-- Prove2me | Theorems.Thm_SemigroupBetti_IsPairAntichain_corank_le
-- name    : SemigroupBetti.IsPairAntichain.corank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:31.4938+00:00
-- url     : https://prove2.me/theorems/5d81a5c1-b2ff-41af-8dd1-c33511668290
-- title:
--   Is Pair Antichain: corank le
-- statement:
--   **Lemma 11 (backward bound).** The number of members whose first coordinate is at least
--   `x.1` is at most `x.2`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L58-L71
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L58-L71

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}

theorem SemigroupBetti.IsPairAntichain.corank_le (hT : IsPairAntichain T) (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2)
    {x : ℕ × ℕ} (hx : x ∈ T) : (T.filter (fun y => x.1 ≤ y.1)).card ≤ x.2 := by sorry
