-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_card_le_of_coord
-- name    : SemigroupBetti.GenData.card_le_of_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:18.328484+00:00
-- url     : https://prove2.me/theorems/216e9f85-5d67-438b-895a-19d3f1619499
-- title:
--   Gen Data: card le of coord
-- statement:
--   A family whose selected `k`-coordinates are injective with values in `[1, c]` has at most
--   `c` members.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L154-L160
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L154-L160

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.card_le_of_coord {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ G.sel d K k ∧ G.sel d K k ≤ c) : F.card ≤ c := by sorry
