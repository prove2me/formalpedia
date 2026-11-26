-- Prove2me | Theorems.Thm_SemigroupBetti_IsPairAntichain_rank_le
-- name    : SemigroupBetti.IsPairAntichain.rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:03:31.106913+00:00
-- url     : https://prove2.me/theorems/d311f68e-3004-4a14-a466-0292f82c9868
-- title:
--   Is Pair Antichain: rank le
-- statement:
--   **Lemma 11 (forward bound).** The number of members whose first coordinate is at most
--   `x.1` (the rank of `x` in the sorted enumeration) is at most `x.1`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L46-L54
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L46-L54

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}

theorem SemigroupBetti.IsPairAntichain.rank_le (hT : IsPairAntichain T) (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2)
    {x : ℕ × ℕ} : (T.filter (fun y => y.1 ≤ x.1)).card ≤ x.1 := by sorry
