-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_pair_le_nu
-- name    : SemigroupBetti.GenData.pair_le_nu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:21.674369+00:00
-- url     : https://prove2.me/theorems/d403b0f8-6c69-4771-af67-d01c0415bc9b
-- title:
--   Gen Data: pair le nu
-- statement:
--   A factorization `y` dominates the "pair" `y k nₖ + y i nᵢ` for `k ≠ i`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L28-L31
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L28-L31

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.pair_le_nu (y : Fin 4 → ℕ) {k i : Fin 4} (hki : k ≠ i) :
    y k * G.n k + y i * G.n i ≤ G.nu y := by sorry
