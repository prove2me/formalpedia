-- Prove2me | Theorems.Thm_SemigroupBetti_IsPairAntichain_exists_rank
-- name    : SemigroupBetti.IsPairAntichain.exists_rank
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:03:32.263122+00:00
-- url     : https://prove2.me/theorems/9a14cd49-138c-5787-8d9b-1d27ec5843f4
-- title:
--   Is Pair Antichain: exists rank
-- statement:
--   **Lemma 11.** In a positive-pair antichain with `k` members, for every `1 ≤ r ≤ k` the
--   `r`-th member in increasing order of first coordinate satisfies `u ≥ r` and `v ≥ k + 1 - r`.
--   (Stated as existence of a member with these bounds; the member is the one of rank `r`.)
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L76-L120
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L76-L120

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}

theorem SemigroupBetti.IsPairAntichain.exists_rank (hT : IsPairAntichain T)
    (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2) {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ T.card) :
    ∃ x ∈ T, r ≤ x.1 ∧ T.card + 1 - r ≤ x.2 := by sorry
